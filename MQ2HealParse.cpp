// MQ2HealParse.cpp : Heavy-lifting combat-line parser for the heal_tracker.lua
// ============================================================================
//
// Purpose
// -------
//   v1.4: adds dual-source chat capture (OnIncomingChat + OnWriteChatColor)
//   with short raw-line de-dupe so the plugin sees the same final combat text
//   GamParse sees without double-counting duplicate callback paths.
//
//   heal_tracker.lua hits a wall in 54-man raids because:
//     * Lua tails the EQ log file every 1-10 ms.
//     * Per poll it can read up to 150,000 lines.
//     * Every line is run through ~10 Lua patterns (the Lua "regex" engine is
//       slow and allocation-heavy compared to native code).
//
//   This plugin moves all of that into C++. It hooks OnIncomingChat() so it
//   sees every combat line EQ generates -- no file polling, no Lua patterns,
//   no risk of double-counting. Parsed events are stored locally AND
//   forwarded to the Lua via a TLO + the MQ2 Actor mailbox system so the
//   existing UI/aggregation/persistence code keeps working unchanged.
//
// Wire-up summary
// ---------------
//   1. Plugin hooks OnIncomingChat().
//   2. Plugin parses heals / damage / spell casts / kills / runes / burns.
//   3. Plugin updates internal counters AND posts a structured event to the
//      Lua side via Actor mailbox "heal_parse_plugin".
//   4. heal_tracker_bridge.lua subscribes to that mailbox and feeds the
//      events into recordHeal/recordDamage/recordSpellCast/onKill.
//   5. Plugin also exposes ${HealParse.*} TLO for direct querying.
//
// Build
// -----
//   Drop this folder into your MacroQuest plugin sources, add it to the
//   solution, build x64-Release. Output: MQ2HealParse.dll.
//   Load with: /plugin mq2healparse
//   Compatible with MacroQuest (Next), VC++ 19+.
//
// ============================================================================

#include <mq/Plugin.h>
#include <imgui.h>

#ifdef _WIN32
#include <windows.h>
#include <d3d11.h>
#include <d3d9.h>
#include <wincodec.h>
#pragma comment(lib, "d3d11.lib")
#pragma comment(lib, "d3d9.lib")
#pragma comment(lib, "windowscodecs.lib")
#endif

#include <algorithm>
#include <atomic>
#include <chrono>
#include <cstdint>
#include <cfloat>
#include <cstdio>
#include <cstring>
#include <cctype>
#include <cstdlib>
#include <ctime>
#include <iomanip>
#include <initializer_list>
#include <fstream>
#include <sstream>
#include <deque>
#include <mutex>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

PreSetup("MQ2HealParse");
PLUGIN_VERSION(1.4);

// ----------------------------------------------------------------------------
// Configuration / globals
// ----------------------------------------------------------------------------

namespace {

// Global HealTracker scrollbar styling - large round knobs for all windows.
static void HP_ApplyGlobalScrollbarStyle()
{
    ImGuiStyle& style = ImGui::GetStyle();
    style.ScrollbarSize = 28.0f;
    style.GrabMinSize = 28.0f;
    style.ScrollbarRounding = 100.0f;
    style.GrabRounding = 100.0f;
}

// Mailbox name the Lua-side bridge will subscribe to.
constexpr const char* kMailboxName = "heal_parse_plugin";

// Minimum heal size to record (matches the Lua default).
std::atomic<int> g_minHealAmount{ 1 };

// If true, the plugin prints every parse hit to the MQ console. Off by default
// for performance.
std::atomic<bool> g_debug{ false };

// Accuracy/audit tooling.  This writes exactly what the plugin counted or
// dropped so it can be compared against GamParse for specific players/classes.
// Commands:
//   /healparse audit on|off
//   /healparse audit player <name|all>
//   /healparse dedup spell on|off
std::atomic<bool> g_auditEnabled{ false };
std::string g_auditPlayerFilter; // empty/all = every player
std::mutex g_auditMutex;
static const char* kAuditLogFolderName = "MQ2HealParse_Audit";
static const char* kAuditLogFileName = "MQ2HealParse_Audit.tsv";

// Per-line context for audit rows. This lets the audit show the exact raw EQ
// combat line that produced each COUNT/DROP/UNMATCHED row.
static thread_local std::string g_auditCurrentRawLine;
static thread_local std::string g_auditCurrentSource;

// Cross-form spell damage de-dupe is useful on clients that emit two different
// lines for one spell hit, but GamParse reads the final EQ log.  Default OFF so
// the plugin counts the same log events GamParse sees.  It can be enabled if a
// server/client is proven to double-emit spell damage in the actual log.
std::atomic<bool> g_spellDamageDedupEnabled{ false };

static bool HP_AuditNameMatches(const std::string& name)
{
    if (g_auditPlayerFilter.empty()) return true;
    if (_stricmp(g_auditPlayerFilter.c_str(), "all") == 0) return true;
    return _stricmp(name.c_str(), g_auditPlayerFilter.c_str()) == 0;
}

static std::string HP_AuditEscape(std::string s)
{
    for (char& c : s) {
        if (c == '\t' || c == '\r' || c == '\n') c = ' ';
    }
    return s;
}

// Forward declaration: audit path helper is defined before the image-loader
// helpers where HP_DirNameA normally lives. Without this, Visual Studio sees
// HP_DirNameA as an unresolved/error expression and the build fails at
// root = HP_DirNameA(dllPath).
static std::string HP_DirNameA(const std::string& path);

static std::string HP_GetAuditPath()
{
#ifdef _WIN32
    std::string root;
    if (gPathMQRoot && gPathMQRoot[0])
        root = gPathMQRoot;
    else {
        char dllPath[MAX_PATH] = { 0 };
        HMODULE hMod = GetModuleHandleA("MQ2HealParse.dll");
        if (hMod && GetModuleFileNameA(hMod, dllPath, MAX_PATH) > 0)
            root = HP_DirNameA(dllPath);
    }
    if (root.empty()) root = ".";
    std::string folder = root + "\\" + kAuditLogFolderName;
    CreateDirectoryA(folder.c_str(), nullptr);
    return folder + "\\" + kAuditLogFileName;
#else
    return std::string(kAuditLogFolderName) + "/" + kAuditLogFileName;
#endif
}

static bool HP_EnsureAuditHeaderUnlocked(std::ofstream& out, const std::string& path)
{
    std::ifstream chk(path, std::ios::binary | std::ios::ate);
    const bool needsHeader = (!chk.good() || chk.tellg() == std::streampos(0));
    if (needsHeader) {
        out << "time\taction\tattacker\towner\ttarget\tamount\ttype\tspell\treason\tsource\traw_line\n";
    }
    return true;
}

static void HP_AuditLine(const char* action,
                         const std::string& attacker,
                         const std::string& owner,
                         const std::string& target,
                         uint64_t amount,
                         const std::string& type,
                         const std::string& spell,
                         const char* reason)
{
    if (!g_auditEnabled.load()) return;
    if (!HP_AuditNameMatches(attacker) && !HP_AuditNameMatches(owner)) return;

    std::lock_guard<std::mutex> lk(g_auditMutex);
    const std::string path = HP_GetAuditPath();
    std::ofstream out(path, std::ios::out | std::ios::app);
    if (!out.good()) {
        WriteChatf("\ar[HealParse]\ax audit write failed: %s", path.c_str());
        return;
    }

    HP_EnsureAuditHeaderUnlocked(out, path);

    std::time_t t = std::time(nullptr);
    out << t << '\t'
        << HP_AuditEscape(action ? action : "") << '\t'
        << HP_AuditEscape(attacker) << '\t'
        << HP_AuditEscape(owner) << '\t'
        << HP_AuditEscape(target) << '\t'
        << amount << '\t'
        << HP_AuditEscape(type) << '\t'
        << HP_AuditEscape(spell) << '\t'
        << HP_AuditEscape(reason ? reason : "") << '\t'
        << HP_AuditEscape(g_auditCurrentSource) << '\t'
        << HP_AuditEscape(g_auditCurrentRawLine) << "\n";
    out.flush();
}


// Master enable. When false, OnIncomingChat is still called but returns early.
// This is the kill switch -- use /healparse off to disable parsing without
// unloading the plugin.
std::atomic<bool> g_enabled{ true };

// Lua-bridge enable. When true, every parsed event is forwarded to the mailbox.
// When false, the plugin still updates internal counters and the TLO, but does
// not push events to Lua. Useful if you want the Lua bridge off but still want
// the TLO numbers.
std::atomic<bool> g_pushToLua{ true };

// C++ EQ log tailer state. Lua sets the path with /healparse logpath and
// enables it with /healparse logtail on. When active, this becomes the single
// DPS source, matching GamParse's EQ-log input without Lua log parsing.
std::string g_logTailPath;
FILE* g_logTailFile = nullptr;
uint64_t g_logTailOffset = 0;
bool g_logTailInitialized = false;
std::atomic<bool> g_logTailEnabled{ false };
std::atomic<uint64_t> g_logTailLines{ 0 };
std::atomic<uint64_t> g_logTailMatched{ 0 };

// Plugin-owned mini live DPS overlay. Lua keeps the full HealTracker UI, but
// the collapsed/mini live DPS window is rendered here in C++ so it does not
// spend any Lua frame time while a fight is active.
std::atomic<bool> g_liveOverlayEnabled{ false };
std::atomic<int>  g_liveOverlayAlphaPercent{ 100 };
std::atomic<bool> g_liveOverlayForceVisible{ false };
std::atomic<bool> g_liveOverlayResetPos{ true };
std::atomic<float> g_liveOverlaySavedX{ -1.0f };
std::atomic<float> g_liveOverlaySavedY{ -1.0f };
std::atomic<bool>  g_liveOverlayPosLoaded{ false };
static const char* kLiveOverlayPosFileName = "MQ2HealParse_MiniPos.tsv";
std::atomic<uint64_t> g_liveOverlayFrames{ 0 };
// Which cycled view is showing: 0 = DPS, 1 = Heals, 2 = Burns/Timers.
std::atomic<int>  g_liveOverlayView{ 0 };

// Futuristic full plugin UI. This is the C++ replacement path for the old Lua
// full window: the mini overlay can stay compact, while this window exposes
// DPS / Heals / Settings from plugin-owned data.
std::atomic<bool> g_fullUiEnabled{ false };
std::atomic<bool> g_fullUiResetPos{ true };
std::atomic<int>  g_fullUiTab{ 1 }; // 0 Heals, 1 DPS, 4 Settings
std::atomic<uint64_t> g_fullUiFrames{ 0 };
static bool g_showCommandsWindow = false;
static bool g_showPetOwnersWindow = false;
static bool g_showBurnTimersWindow = false;

void CloseLogTailer();
bool OpenLogTailerIfNeeded();
void TailPluginLog();


// Mutex guarding all the maps below. Held briefly only while updating.
std::mutex g_statsMutex;

// --- aggregate counters (used by the TLO; the Lua side keeps its own copy) ---
struct HealerStats {
    uint64_t total = 0;
    uint32_t count = 0;
    uint32_t max   = 0;
};
struct TargetHealStats {
    uint64_t total = 0;
    uint32_t count = 0;
    uint32_t max   = 0;
    std::unordered_map<std::string, HealerStats> healers;
};
struct AttackerStats {
    uint64_t total = 0;
    uint32_t count = 0;
    uint32_t max   = 0;
};

std::unordered_map<std::string, TargetHealStats> g_healByTarget;
std::unordered_map<std::string, AttackerStats>   g_damageByAttacker;
std::unordered_map<std::string, uint32_t>        g_spellCastsByCaster;
std::unordered_map<std::string, uint32_t>        g_spellCastsBySpell;

// Recent-spell-cast cache for anonymous-DoT-tick attribution. Bounded.
struct RecentCast {
    std::string caster;
    int64_t     atMs;
};
std::unordered_map<std::string, RecentCast> g_recentSpellCasts;

// Known PC names. Populated as a side-effect of seeing heals/damage from
// something that looks like a player. Used to filter mob->mob and mob->PC
// damage out of the group-DPS stream.
std::unordered_set<std::string> g_knownChars;

// Persistent player-name -> class abbreviation cache.
// Once a player class is detected in-zone, keep it forever so saved fights
// still show the class text and PNG emblem even when the player is no longer
// in the same zone or after the plugin is reloaded.
std::unordered_map<std::string, std::string> g_playerClassCache;
std::mutex g_playerClassCacheMutex;
static const char* kPlayerClassCacheFileName = "MQ2HealParse_PlayerClasses.tsv";

// User-supplied pet-name -> owner map. /healparse pet add <pet> <owner>
std::unordered_map<std::string, std::string> g_petOwners;

// Active drivers. Mailbox events are posted on every line, but only the
// driver's Lua side should call recordDamage/recordHeal. We don't gate that
// here -- the bridge does. Plugin parses on every box.

// Stats counters for the TLO.
std::atomic<uint64_t> g_linesSeen{ 0 };
std::atomic<uint64_t> g_linesMatched{ 0 };
std::atomic<uint64_t> g_eventsPosted{ 0 };
std::atomic<uint64_t> g_linesFromIncoming{ 0 };
std::atomic<uint64_t> g_linesFromWriteChat{ 0 };
std::atomic<uint64_t> g_linesDeduped{ 0 };

// Wallclock-ish monotonic ms.
int64_t NowMs() {
    using namespace std::chrono;
    return duration_cast<milliseconds>(steady_clock::now().time_since_epoch()).count();
}

// ----------------------------------------------------------------------------
// String helpers. Hand-rolled, branch-free where it matters. These are the
// hot path: we'd rather inline tight char* scans than build std::regex.
// ----------------------------------------------------------------------------

// Strip "[Sun Nov 09 22:32:14 2025] " prefix if present. Returns a pointer
// into the same buffer.
const char* StripLogTimestamp(const char* line) {
    if (line[0] != '[') return line;
    const char* close = std::strchr(line, ']');
    if (!close) return line;
    const char* p = close + 1;
    while (*p == ' ' || *p == '\t') ++p;
    return p;
}

// Trim trailing whitespace and a trailing period. Mutates s.
void RTrim(std::string& s) {
    while (!s.empty()) {
        char c = s.back();
        if (c == ' ' || c == '\t' || c == '.' || c == '!' || c == ',') {
            s.pop_back();
        } else {
            break;
        }
    }
}
void LTrim(std::string& s) {
    size_t i = 0;
    while (i < s.size() && (s[i] == ' ' || s[i] == '\t')) ++i;
    if (i) s.erase(0, i);
}
void Trim(std::string& s) { RTrim(s); LTrim(s); }

bool StartsWith(const char* haystack, const char* needle) {
    while (*needle) {
        if (*haystack != *needle) return false;
        ++haystack; ++needle;
    }
    return true;
}

bool IStartsWith(const char* haystack, const char* needle) {
    while (*needle) {
        char a = *haystack, b = *needle;
        if (a >= 'A' && a <= 'Z') a = a - 'A' + 'a';
        if (b >= 'A' && b <= 'Z') b = b - 'A' + 'a';
        if (a != b) return false;
        ++haystack; ++needle;
    }
    return true;
}

// memmem-ish for non-POSIX. Returns nullptr or pointer to first match.
const char* FindSubstr(const char* haystack, const char* needle) {
    return std::strstr(haystack, needle);
}

bool ContainsCI(const char* haystack, const char* needle) {
    // Naive case-insensitive search. Good enough for short needles.
    size_t nlen = std::strlen(needle);
    if (nlen == 0) return true;
    for (const char* p = haystack; *p; ++p) {
        size_t i = 0;
        while (i < nlen) {
            char a = p[i], b = needle[i];
            if (!a) return false;
            if (a >= 'A' && a <= 'Z') a = a - 'A' + 'a';
            if (b >= 'A' && b <= 'Z') b = b - 'A' + 'a';
            if (a != b) break;
            ++i;
        }
        if (i == nlen) return true;
    }
    return false;
}


std::string LowerCopy(std::string s) {
    for (char& c : s) {
        if (c >= 'A' && c <= 'Z') c = c - 'A' + 'a';
    }
    return s;
}

bool IsNecroDotSpell(const std::string& spellName) {
    std::string s = LowerCopy(spellName);
    Trim(s);
    return s == "venom of anguish"
        || s == "splort"
        || s == "splurt"
        || s == "chaos plague"
        || s == "blood of thule"
        || s == "pyre of mori"
        || s == "dark nightmare"
        || s == "horror"
        || s == "dread pyre"
        || s == "chaos venom"
        || s == "ancient: curse of mori"
        || s == "gathering dusk"
        || s == "funeral pyre of kelador"
        || s == "bond of forsaken soul"
        || s == "night fire"
        || s == "dark plague"
        || s == "fang of death";
}

// Parse a non-negative integer with embedded commas. Returns false on no digits.
// On success, *end points to the first char past the number.
bool ParseUintWithCommas(const char* s, uint64_t* out, const char** end) {
    uint64_t v = 0;
    const char* p = s;
    bool any = false;
    while (*p) {
        char c = *p;
        if (c >= '0' && c <= '9') {
            v = v * 10 + (uint64_t)(c - '0');
            any = true;
        } else if (c == ',') {
            // skip
        } else {
            break;
        }
        ++p;
    }
    if (!any) return false;
    *out = v;
    if (end) *end = p;
    return true;
}

// Looks like a PC name? Single capitalized word, 3+ chars, no leading article.
bool LooksLikePcName(const std::string& s) {
    if (s.size() < 3) return false;
    if (s.find(' ') != std::string::npos) return false;
    char c0 = s[0];
    if (!(c0 >= 'A' && c0 <= 'Z')) return false;
    // Reject leading articles.
    if (s.size() >= 2 && (s.compare(0, 2, "A ") == 0)) return false;
    if (s.size() >= 3 && (s.compare(0, 3, "An ") == 0 || s.compare(0, 3, "an ") == 0
                          || s.compare(0, 3, "a ") == 0)) return false;
    if (s.size() >= 4 && (s.compare(0, 4, "The ") == 0 || s.compare(0, 4, "the ") == 0)) return false;
    return true;
}

static void HP_SavePetOwnersUnlocked();

bool IsKnownPet(const std::string& name) {
    if (g_petOwners.empty()) return false;
    if (g_petOwners.count(name)) return true;
    // Case-insensitive scan.
    std::string lower = name;
    for (char& c : lower) if (c >= 'A' && c <= 'Z') c = c - 'A' + 'a';
    for (auto& kv : g_petOwners) {
        std::string k = kv.first;
        for (char& c : k) if (c >= 'A' && c <= 'Z') c = c - 'A' + 'a';
        if (k == lower) return true;
    }
    return false;
}

// "<owner>`s pet" / "<owner>'s pet" / "<owner>’s pet" / warder / ward /
// Animated Corpse / doppelganger / swarm -> "<owner>". Returns original on
// no match.  Swarm pets such as "Eyehop's pet" are auto-linked into
// g_petOwners so the Player Damage Split Pets / Combine Pets button can
// separate or merge them without manual linking.
std::string AttributeDamage(const std::string& attacker) {
    if (attacker.empty()) return "unknown";

    // First try persistent/manual pet map.
    auto it = g_petOwners.find(attacker);
    if (it != g_petOwners.end()) return it->second;
    std::string lower = attacker;
    for (char& c : lower) if (c >= 'A' && c <= 'Z') c = c - 'A' + 'a';
    for (auto& kv : g_petOwners) {
        std::string k = kv.first;
        for (char& c : k) if (c >= 'A' && c <= 'Z') c = c - 'A' + 'a';
        if (k == lower) return kv.second;
    }

    // Find possessive marker. EQ commonly uses backtick, but logs/UIs can also
    // contain a straight apostrophe or a smart apostrophe.
    size_t apos = std::string::npos;
    size_t markerLen = 3; // `s  or 's
    for (size_t i = 0; i < attacker.size(); ++i) {
        if (attacker[i] == '`' || attacker[i] == '\'') {
            if (i + 2 < attacker.size() && attacker[i + 1] == 's' && attacker[i + 2] == ' ') {
                apos = i; markerLen = 3; break;
            }
        }
    }
    if (apos == std::string::npos) {
        size_t smart = attacker.find("\xE2\x80\x99s "); // ’s
        if (smart != std::string::npos) {
            apos = smart;
            markerLen = 5; // 3-byte apostrophe + s + space
        }
    }
    if (apos == std::string::npos) return attacker;

    std::string owner = attacker.substr(0, apos);
    std::string suffix = attacker.substr(apos + markerLen);
    Trim(owner);
    Trim(suffix);

    // Lowercase suffix for keyword match.
    std::string suf = suffix;
    for (char& c : suf) if (c >= 'A' && c <= 'Z') c = c - 'A' + 'a';

    const bool isPetLike =
        suf == "pet" || suf == "warder" || suf == "ward"
        || suf == "animated corpse" || suf == "doppelganger"
        || suf == "swarm" || suf.find("pet") != std::string::npos
        || suf.find("warder") != std::string::npos
        || suf.find("swarm") != std::string::npos
        || suf.find("corpse") != std::string::npos
        || suf.find("doppelganger") != std::string::npos
        || suf.find("illusion") != std::string::npos
        || suf.find("servant") != std::string::npos
        || suf.find("minion") != std::string::npos;

    if (isPetLike && !owner.empty()) {
        // Auto-link ALL runtime swarm/possessive pets for every raid member.
        // Any attacker named like "Zaxbys's pet" / "Zaxbys`s pet" /
        // "Zaxbys’s pet" is forced to owner "Zaxbys" immediately, even if
        // that player was never manually linked or seen before.
        const bool isNewLink = (g_petOwners.find(attacker) == g_petOwners.end());
        g_petOwners[attacker] = owner;
        g_knownChars.insert(owner);
        if (isNewLink) HP_SavePetOwnersUnlocked();
        return owner;
    }

    // Generic possessive but only if owner is already known.
    if (g_knownChars.count(owner)) return owner;
    return attacker;
}

// ----------------------------------------------------------------------------
// Charm-pet resolution via the spawn manager.
//
// EQ's combat log carries only display names. Two same-named mobs (a hostile
// "froglok bok knight" and a charmed "froglok bok knight") look identical in
// chat. They are NOT identical in the spawn manager: the charmed one's
// MasterID points at a player, the hostile one's is zero. We disambiguate
// by walking pSpawnManager when needed.
//
// The cache is intentionally short (250ms) so a charm-break-and-recharm cycle
// re-resolves quickly. All cache mutations are protected by their own mutex
// (g_petOwnerCacheMutex) so callers do NOT need to hold g_statsMutex.
//
// Thread safety: pSpawnManager is owned by the EQ main thread. OnIncomingChat
// runs on the main thread, so this is safe. Do NOT call these from a worker.
// ----------------------------------------------------------------------------

// Forward decl so ResolveAttacker (defined below) can call NoteKnownChar.
void NoteKnownChar(const std::string& name);

struct PetOwnerCacheEntry {
    std::string owner;     // empty string = "not a player-owned pet"
    int64_t     expiryMs = 0;
};
std::unordered_map<std::string, PetOwnerCacheEntry> g_petOwnerCache;
std::mutex g_petOwnerCacheMutex;

constexpr int64_t kPetOwnerCacheTtlMs = 250;

// Resolve a display name to a player owner via the spawn manager. Returns
// the owner's name when the spawn is an NPC controlled by a player, or empty
// string when not (no spawn / hostile NPC / spawn is itself a player).
std::string LookupCharmedPetOwner(const std::string& displayName) {
    if (displayName.empty()) return {};

    int64_t now = NowMs();
    {
        std::lock_guard<std::mutex> lk(g_petOwnerCacheMutex);
        auto it = g_petOwnerCache.find(displayName);
        if (it != g_petOwnerCache.end() && it->second.expiryMs > now) {
            return it->second.owner;
        }
    }

    std::string owner;  // default: not a pet

    // Walk the spawn list ourselves. GetSpawnByName returns the first match;
    // when two spawns share a name we need to find the player-owned one if it
    // exists. This is the core fix - GetSpawnByName alone can't disambiguate.
    PlayerClient* chosen = nullptr;
    if (pSpawnManager) {
        for (PlayerClient* cur = pSpawnManager->FirstSpawn; cur; cur = cur->GetNext()) {
            if (cur->Type != SPAWN_NPC) continue;

            // Match on either DisplayedName (chat-visible form) or Name
            // (underlying name). Charmed mobs sometimes get renamed in one
            // but not the other depending on server/spell.
            const char* dn = cur->DisplayedName;
            const char* nm = cur->Name;
            bool nameMatch =
                (dn && dn[0] && displayName == dn) ||
                (nm && nm[0] && displayName == nm);
            if (!nameMatch) continue;

            if (cur->MasterID != 0) {
                PlayerClient* master = GetSpawnByID(cur->MasterID);
                if (master && master->Type == SPAWN_PLAYER) {
                    chosen = cur;
                    break;  // found the player-owned one; stop searching
                }
            }
            if (!chosen) chosen = cur;  // remember best non-pet match as fallback
        }
    }

    if (chosen && chosen->Type == SPAWN_NPC && chosen->MasterID != 0) {
        PlayerClient* master = GetSpawnByID(chosen->MasterID);
        if (master && master->Type == SPAWN_PLAYER && master->Name[0]) {
            owner.assign(master->Name);
        }
    }

    {
        std::lock_guard<std::mutex> lk(g_petOwnerCacheMutex);
        g_petOwnerCache[displayName] = { owner, now + kPetOwnerCacheTtlMs };
    }
    return owner;
}

// Returns true if EVERY in-zone spawn matching `displayName` is a player-
// owned pet. Returns false if any hostile counterpart exists, or if no
// spawn matches (we have no proof either way; let the caller register the
// event rather than risk dropping a real fight).
bool HasOnlyCharmedSpawn(const std::string& displayName) {
    if (displayName.empty() || !pSpawnManager) return false;

    bool foundAny = false;
    bool foundHostile = false;
    for (PlayerClient* cur = pSpawnManager->FirstSpawn; cur; cur = cur->GetNext()) {
        if (cur->Type != SPAWN_NPC) continue;
        const char* dn = cur->DisplayedName;
        const char* nm = cur->Name;
        if (!((dn && dn[0] && displayName == dn) || (nm && nm[0] && displayName == nm))) continue;

        foundAny = true;
        if (cur->MasterID == 0) { foundHostile = true; break; }
        PlayerClient* master = GetSpawnByID(cur->MasterID);
        if (!master || master->Type != SPAWN_PLAYER) { foundHostile = true; break; }
    }
    return foundAny && !foundHostile;
}

// Invalidate the cache. Called on zone change.
void ClearPetOwnerCache() {
    std::lock_guard<std::mutex> lk(g_petOwnerCacheMutex);
    g_petOwnerCache.clear();
}

// Single entry point for attacker -> owner resolution. Parsers call this
// instead of AttributeDamage directly. Resolution order:
//   1. Possessive form / user-supplied map (AttributeDamage).
//   2. Spawn-aware charm lookup.
//   3. Return attacker unchanged.
//
// `wasCharmed` (optional) lets callers know whether the spawn lookup matched.
// Useful for gating the "ok" flag in parsers so charmed pet damage flows
// even when the owner isn't yet in g_knownChars.
std::string ResolveAttacker(const std::string& attacker, bool* wasCharmed = nullptr) {
    if (wasCharmed) *wasCharmed = false;
    if (attacker.empty()) return "unknown";

    std::string viaMap = AttributeDamage(attacker);
    if (viaMap != attacker) return viaMap;

    std::string owner = LookupCharmedPetOwner(attacker);
    if (!owner.empty()) {
        NoteKnownChar(owner);
        if (wasCharmed) *wasCharmed = true;
        return owner;
    }
    return attacker;
}

// ----------------------------------------------------------------------------
// Mailbox plumbing. We use MQ2 Actors so the Lua side can subscribe with
// Actors.register('heal_parse_plugin', ...). Each event is a small string-
// keyed table. Lua wraps the access through pcall.
//
// Rather than depend on the actors C++ API (which has churned between MQ
// versions), we just send a structured /chat-style line through a private
// hook. The bridge Lua picks it up via a single mq.event() listener with
// a very narrow pattern.
//
// This keeps the plugin source MQ-version-agnostic: it works on any build
// with OnIncomingChat() + WriteChatColor(). The bridge filters its own
// emissions out of the parse path so we don't loop.
//
// Format:
//   /hpevt|<kind>|<k=v>|<k=v>|...
// Keys never contain | or = since they come from controlled fields, and we
// percent-escape | and = and \n in values.
// ----------------------------------------------------------------------------

void EscapeEventValue(std::string& v) {
    std::string out;
    out.reserve(v.size() + 4);
    for (char c : v) {
        if (c == '|') out += "%7C";
        else if (c == '=') out += "%3D";
        else if (c == '\n' || c == '\r') out += ' ';
        else out += c;
    }
    v.swap(out);
}

// ----------------------------------------------------------------------------
// Event queue.
//
// The bridge polls ${HealParse.Drain[N]} every main-loop tick. Each call
// pops up to N events and returns them as newline-joined strings of the
// form "kind|k=v|k=v|...". The bridge splits and dispatches.
//
// We use a bounded deque protected by its own mutex. Bounded to avoid
// unbounded growth if the bridge stops draining (e.g. /lua stop) - in
// that case we drop the oldest events. 16k cap is plenty for raid-scale
// burst then catch-up; at ~300 events/sec that's 50+ seconds of buffer.
// ----------------------------------------------------------------------------
constexpr size_t kMaxQueueDepth = 524288;
std::deque<std::string> g_eventQueue;
std::mutex g_eventQueueMutex;

void FlushDamageBatch(bool force);

void EnqueueEvent(std::string&& line) {
    std::lock_guard<std::mutex> lk(g_eventQueueMutex);
    if (g_eventQueue.size() >= kMaxQueueDepth) {
        // Drop oldest. Bridge will see a gap but the alternative is OOM.
        g_eventQueue.pop_front();
    }
    g_eventQueue.emplace_back(std::move(line));
}

// Drain up to maxEvents events, joining with '\n'. Called from the TLO.
std::string DrainEventQueue(size_t maxEvents) {
    FlushDamageBatch(false);
    std::string out;
    std::lock_guard<std::mutex> lk(g_eventQueueMutex);
    size_t take = (maxEvents == 0 || maxEvents > g_eventQueue.size())
                      ? g_eventQueue.size()
                      : maxEvents;
    if (take == 0) return out;

    // Pre-reserve a reasonable buffer to minimize reallocs.
    size_t approx = 0;
    {
        auto it = g_eventQueue.begin();
        for (size_t i = 0; i < take; ++i, ++it) approx += it->size() + 1;
    }
    out.reserve(approx);

    for (size_t i = 0; i < take; ++i) {
        if (i) out += '\n';
        out += g_eventQueue.front();
        g_eventQueue.pop_front();
    }
    return out;
}

// Fast damage snapshot aggregation.  The old path enqueued one Lua event for
// every swing/nuke/DoT tick.  In a raid that can be thousands of Lua calls per
// second, which makes HealTracker trail GamParse.  Damage is now accumulated in
// C++ by attacker+target+type and emitted as compact damage_batch rows.  Non-
// damage events force a flush first so kills/history cannot pass pending damage.
struct DamageBatchStats {
    uint64_t amount = 0;
    uint32_t count = 0;
    uint32_t maxHit = 0;
    std::string attacker;
    std::string target;
    std::string type;
};

std::unordered_map<std::string, DamageBatchStats> g_damageBatch;
std::vector<std::string> g_damageBatchOrder;
std::mutex g_damageBatchMutex;
int64_t g_lastDamageBatchFlushMs = 0;
constexpr int64_t kDamageBatchFlushMs = 250; // 4 updates/sec into Lua; UI still snapshots once/sec


// ----------------------------------------------------------------------------
// Plugin-owned live DPS tracker state.
// ----------------------------------------------------------------------------
// The Lua UI should not calculate live DPS from every hit. The plugin keeps the
// active fight totals here and exposes a compact snapshot through
// ${HealParse.LiveDPS}. Lua can draw the same mini tracker using this one string
// without running per-hit live-DPS math.
struct LiveDpsRow {
    uint64_t total = 0;
    uint64_t melee = 0;
    uint64_t spell = 0;
    uint64_t dot = 0;
    uint64_t proc = 0;
    uint64_t pet = 0;
    uint64_t swarm = 0;
    uint64_t other = 0;
    uint32_t count = 0;
    uint32_t maxHit = 0;
    int64_t  maxHitWall = 0; // exact wall-clock time the player's best spike happened
};

struct HPPcDeathRow {
    std::string player;
    std::string killer;
    int64_t ms = 0;
    int64_t wall = 0;
    uint64_t recentDamage = 0;
};

struct HP_DpsSpikeEvent {
    std::string player;
    std::string target;
    std::string type;
    uint64_t amount = 0;
    int64_t ms = 0;
    int64_t wall = 0;
};

struct LiveDpsFight {
    std::string mob;
    int mobRace = 0;
    int mobBodyType = 0;
    std::string mobIconKey;
    int64_t startedMs = 0;
    int64_t lastDamageMs = 0;
    int64_t wallStarted = 0;
    int64_t wallEnded = 0;
    uint64_t total = 0;
    std::unordered_map<std::string, LiveDpsRow> players;
    std::vector<HPPcDeathRow> deaths;
    std::vector<std::string> logs;
    std::vector<HP_DpsSpikeEvent> dpsSpikes;
    std::unordered_map<std::string, uint32_t> spellCasts; // spells cast during this fight only
    std::unordered_map<std::string, std::unordered_map<std::string, uint32_t>> spellCastsByCaster; // caster -> spell -> casts during this fight
};

LiveDpsFight g_liveDps;
std::mutex g_liveDpsMutex;

struct CompletedDpsFight {
    std::string mob;
    int mobRace = 0;
    int mobBodyType = 0;
    std::string mobIconKey;
    int64_t startedMs = 0;
    int64_t endedMs = 0;
    int64_t wallStarted = 0;
    int64_t wallEnded = 0;
    uint64_t total = 0;
    std::unordered_map<std::string, LiveDpsRow> players;
    std::vector<HPPcDeathRow> deaths;
    std::vector<std::string> logs;
    std::vector<HP_DpsSpikeEvent> dpsSpikes;
    std::unordered_map<std::string, uint32_t> spellCasts; // saved spell casts for this fight only
    std::unordered_map<std::string, std::unordered_map<std::string, uint32_t>> spellCastsByCaster; // saved caster -> spell -> casts for this fight
};

std::vector<CompletedDpsFight> g_completedDpsFights;
std::mutex g_completedDpsMutex;
std::atomic<int> g_fullUiDpsSelectedFight{ -1 }; // -1 = active/live fight; >=0 = completed fight index
constexpr size_t kMaxCompletedDpsFights = 300;

struct HP_PendingDpsSpellCast {
    std::string caster;
    std::string spell;
    int64_t ms = 0;
};
std::vector<HP_PendingDpsSpellCast> g_pendingDpsSpellCasts;
std::mutex g_pendingDpsSpellMutex;

// DPS UI filters + persistent completed-fight archive.
// This keeps completed parses available after plugin rebuild/reload instead of
// losing them every time MQ2HealParse is updated.
static char g_dpsMobSearch[128] = "";
static char g_dpsDateFrom[32] = "";
static char g_dpsDateTo[32] = "";
static int  g_dpsMinDamageFilter = 0;
static int  g_dpsDurationFilter = 0; // 0 any, 1 <30s, 2 30-60s, 3 60-120s, 4 >120s
static char g_dpsGroupFilter[64] = "All Groups";
static bool g_dpsRangeMode = false;
static int  g_dpsRangeStart = -1;
static bool g_dpsSelectAllToggle = false;
static bool g_dpsCombinePets = true; // true = linked pets are merged into owner rows in Player Damage
static std::unordered_set<int> g_dpsSelectedFights;
static const char* kDpsHistoryFileName = "MQ2HealParse_DPSHistory.tsv";
static const char* kMobIconCacheFileName = "MQ2HealParse_MobIconCache.tsv";

// Post-kill lag guard: history/cache files are NOT written during fight archive.
// Archive happens on kill/timeout/new-target and must stay memory-only.  These
// flags let OnPulse save later during downtime, spread across frames.
std::atomic<bool> g_dpsHistoryDirty{ false };
std::atomic<bool> g_healHistoryDirty{ false };
std::atomic<int64_t> g_historyDirtyAtMs{ 0 };
std::atomic<int64_t> g_lastDeferredHistorySaveMs{ 0 };
constexpr int64_t kDeferredHistorySaveDelayMs = 15000;
constexpr int64_t kDeferredHistorySaveGapMs = 5000;

static const char* kPetOwnersFileName = "MQ2HealParse_PetOwners.tsv";
static const char* kHealHistoryFileName = "MQ2HealParse_HealHistory.tsv";
static const char* kBurnTriggersFileName = "MQ2HealParse_BurnTimers.tsv";

static std::string HP_TrimCopy(std::string s)
{
    size_t a = s.find_first_not_of(" \t\r\n\"");
    if (a == std::string::npos) return std::string();
    size_t b = s.find_last_not_of(" \t\r\n\"");
    return s.substr(a, b - a + 1);
}

static std::string HP_EscapePetOwnerField(const std::string& v)
{
    std::string out;
    out.reserve(v.size() + 8);
    for (char c : v) {
        if (c == '\\') out += "\\\\";
        else if (c == '\t') out += "\\t";
        else if (c == '\n') out += "\\n";
        else if (c == '\r') out += "\\r";
        else out.push_back(c);
    }
    return out;
}

static std::string HP_UnescapePetOwnerField(const std::string& v)
{
    std::string out;
    out.reserve(v.size());
    bool esc = false;
    for (char c : v) {
        if (esc) {
            if (c == 't') out.push_back('\t');
            else if (c == 'n') out.push_back('\n');
            else if (c == 'r') out.push_back('\r');
            else out.push_back(c);
            esc = false;
        } else if (c == '\\') {
            esc = true;
        } else {
            out.push_back(c);
        }
    }
    if (esc) out.push_back('\\');
    return out;
}


static void HP_SaveMiniOverlayPos(float x, float y)
{
    if (x < 0.0f || y < 0.0f) return;
    std::ofstream out(kLiveOverlayPosFileName, std::ios::out | std::ios::trunc);
    if (!out.good()) return;
    out << x << '\t' << y << "\n";
}

static void HP_LoadMiniOverlayPos()
{
    if (g_liveOverlayPosLoaded.exchange(true)) return;

    std::ifstream in(kLiveOverlayPosFileName);
    if (!in.good()) return;

    float x = -1.0f, y = -1.0f;
    in >> x >> y;
    if (x >= 0.0f && y >= 0.0f) {
        g_liveOverlaySavedX.store(x);
        g_liveOverlaySavedY.store(y);
        g_liveOverlayResetPos.store(false);
    }
}

static ImVec2 HP_GetCenteredFullUiPos()
{
    ImGuiIO& io = ImGui::GetIO();
    float w = 1500.0f;
    float h = 860.0f;

    if (io.DisplaySize.x > 0.0f) w = std::min(w, io.DisplaySize.x - 40.0f);
    if (io.DisplaySize.y > 0.0f) h = std::min(h, io.DisplaySize.y - 80.0f);

    float x = 90.0f;
    float y = 70.0f;
    if (io.DisplaySize.x > 0.0f) x = std::max(20.0f, (io.DisplaySize.x - w) * 0.5f);
    if (io.DisplaySize.y > 0.0f) y = std::max(45.0f, (io.DisplaySize.y - h) * 0.5f);
    return ImVec2(x, y);
}

static ImVec2 HP_GetSafeFullUiSize()
{
    ImGuiIO& io = ImGui::GetIO();
    float w = 1500.0f;
    float h = 860.0f;
    if (io.DisplaySize.x > 0.0f) w = std::min(w, io.DisplaySize.x - 40.0f);
    if (io.DisplaySize.y > 0.0f) h = std::min(h, io.DisplaySize.y - 80.0f);
    return ImVec2(std::max(1180.0f, w), std::max(700.0f, h));
}

static void HP_SavePetOwnersUnlocked()
{
    std::ofstream out(kPetOwnersFileName, std::ios::out | std::ios::trunc);
    if (!out.good()) return;
    out << "# HealParse Pet Owners v1\n";
    for (const auto& kv : g_petOwners) {
        out << HP_EscapePetOwnerField(kv.first) << '\t' << HP_EscapePetOwnerField(kv.second) << "\n";
    }
}

static void HP_LoadPetOwners()
{
    std::ifstream in(kPetOwnersFileName);
    if (!in.good()) return;

    std::lock_guard<std::mutex> lk(g_statsMutex);
    std::string line;
    while (std::getline(in, line)) {
        if (line.empty() || line[0] == '#') continue;
        size_t tab = line.find('\t');
        if (tab == std::string::npos) continue;
        std::string pet = HP_TrimCopy(HP_UnescapePetOwnerField(line.substr(0, tab)));
        std::string owner = HP_TrimCopy(HP_UnescapePetOwnerField(line.substr(tab + 1))); 
        if (pet.empty() || owner.empty()) continue;
        g_petOwners[pet] = owner;
        g_knownChars.insert(owner);
    }
}

static void HP_SetPetOwner(const std::string& petName, const std::string& ownerName, bool saveNow = true)
{
    std::string pet = HP_TrimCopy(petName);
    std::string owner = HP_TrimCopy(ownerName);
    if (pet.empty() || owner.empty()) {
        WriteChatf("\ar[HealParse]\ax usage: /healparse pet link <owner> <pet name>");
        return;
    }

    std::lock_guard<std::mutex> lk(g_statsMutex);
    g_petOwners[pet] = owner;
    g_knownChars.insert(owner);
    if (saveNow) HP_SavePetOwnersUnlocked();
    WriteChatf("\ag[HealParse]\ax pet linked: %s -> %s", pet.c_str(), owner.c_str());
}

static std::string HP_GetLinkedPetOwnerForDisplay(const std::string& name)
{
    if (name.empty()) return name;
    std::lock_guard<std::mutex> lk(g_statsMutex);

    auto it = g_petOwners.find(name);
    if (it != g_petOwners.end() && !it->second.empty())
        return it->second;

    std::string lowerName = LowerCopy(name);
    for (const auto& kv : g_petOwners) {
        if (LowerCopy(kv.first) == lowerName && !kv.second.empty())
            return kv.second;
    }
    return name;
}

static std::string HP_CanonicalNpcCompareName(std::string s)
{
    s = HP_TrimCopy(s);
    for (char& c : s) {
        if (c >= 'A' && c <= 'Z') c = c - 'A' + 'a';
        // EQ names sometimes vary only by apostrophe style/backtick.
        if (c == '`' || c == '\'') c = '\'';
    }

    // History/live target matching must not split one mob into different
    // fights just because one combat line says "A ..." while another says
    // "a ..." / "an ..." / "the ...".  That mismatch caused melee lines to
    // be dropped as off-target, leaving the DPS type graph showing Spell only.
    auto stripArticle = [](std::string& v) {
        if (v.rfind("a ", 0) == 0) v.erase(0, 2);
        else if (v.rfind("an ", 0) == 0) v.erase(0, 3);
        else if (v.rfind("the ", 0) == 0) v.erase(0, 4);
    };
    stripArticle(s);
    return HP_TrimCopy(s);
}

static bool HP_SameNameNoCase(const std::string& a, const std::string& b)
{
    if (a.empty() || b.empty()) return false;
    return HP_CanonicalNpcCompareName(a) == HP_CanonicalNpcCompareName(b);
}

static bool HP_IsInvalidFightTargetName(const std::string& name)
{
    std::string n = LowerCopy(HP_TrimCopy(name));
    if (n.empty()) return true;

    // These are not mob names. They come from EQ lines such as:
    //   "Dorias hit by non-melee for 87 points of damage"
    // Without this guard, the parser can accidentally create fights named
    // "hit by non-melee" or "by non-melee".
    if (n == "hit by non-melee" || n == "by non-melee" || n == "was hit by non-melee") return true;
    if (n.find("non-melee") != std::string::npos &&
        (n.find("hit") != std::string::npos || n.find("by") != std::string::npos)) return true;

    return false;
}

static bool HP_ShouldHideDpsDisplayRow(const std::string& rowName, const std::string& mobName)
{
    if (rowName.empty()) return true;
    if (mobName.empty()) return false;

    // Never show the active/selected mob as if it were a player in Player Damage,
    // Live DPS, or the after-fight popup. This catches stray mob->player or
    // mob->mob combat lines that sometimes leak into the DPS stream.
    if (HP_SameNameNoCase(rowName, mobName)) return true;

    // Some EQ log lines can shorten the mob name when it leaks into the attacker
    // field. Example: target/fight name is "DPS Machine" but the damage row shows
    // attacker "DPS". Hide those partial mob-name leaks from Player Damage.
    std::string rowLower = LowerCopy(HP_TrimCopy(rowName));
    std::string mobLower = LowerCopy(HP_TrimCopy(mobName));
    if (!rowLower.empty() && !mobLower.empty()) {
        if (mobLower.size() > rowLower.size()
            && mobLower.compare(0, rowLower.size(), rowLower) == 0
            && (mobLower[rowLower.size()] == ' ' || mobLower[rowLower.size()] == '\'' || mobLower[rowLower.size()] == '-' || mobLower[rowLower.size()] == '_')) {
            return true;
        }
        if (rowLower.size() > mobLower.size()
            && rowLower.compare(0, mobLower.size(), mobLower) == 0
            && (rowLower[mobLower.size()] == ' ' || rowLower[mobLower.size()] == '\'' || rowLower[mobLower.size()] == '-' || rowLower[mobLower.size()] == '_')) {
            return true;
        }
    }

    // Also hide linked pet names that resolve back to the mob name.
    std::string owner = HP_GetLinkedPetOwnerForDisplay(rowName);
    if (owner != rowName && HP_SameNameNoCase(owner, mobName)) return true;
    return false;
}

static std::string HP_GetPetCombinedDisplayName(const std::string& name)
{
    return g_dpsCombinePets ? HP_GetLinkedPetOwnerForDisplay(name) : name;
}

static std::vector<std::pair<std::string, std::string>> HP_GetPetOwnerLinksForUi()
{
    std::vector<std::pair<std::string, std::string>> out;
    std::lock_guard<std::mutex> lk(g_statsMutex);
    out.reserve(g_petOwners.size());
    for (const auto& kv : g_petOwners)
        out.push_back({ kv.first, kv.second });
    std::sort(out.begin(), out.end(), [](const auto& a, const auto& b) {
        if (a.second == b.second) return a.first < b.first;
        return a.second < b.second;
    });
    return out;
}

static bool HP_LooksLikePossessivePetName(const std::string& name)
{
    std::string n = LowerCopy(HP_TrimCopy(name));
    if (n.empty()) return false;
    return n.find("`s pet") != std::string::npos
        || n.find("'s pet") != std::string::npos
        || n.find("’s pet") != std::string::npos
        || n.find("`s warder") != std::string::npos
        || n.find("'s warder") != std::string::npos
        || n.find("’s warder") != std::string::npos
        || n.find("`s doppelganger") != std::string::npos
        || n.find("'s doppelganger") != std::string::npos
        || n.find("’s doppelganger") != std::string::npos;
}

static void HP_AddUniqueName(std::vector<std::string>& list, const std::string& name)
{
    std::string n = HP_TrimCopy(name);
    if (n.empty()) return;
    for (const std::string& existing : list) {
        if (HP_SameNameNoCase(existing, n)) return;
    }
    list.push_back(n);
}

static void HP_GetPetOwnerPickerLists(std::vector<std::string>& pets, std::vector<std::string>& owners)
{
    pets.clear();
    owners.clear();

    {
        std::lock_guard<std::mutex> lk(g_statsMutex);
        for (const auto& kv : g_petOwners) {
            HP_AddUniqueName(pets, kv.first);
            HP_AddUniqueName(owners, kv.second);
        }
        for (const std::string& n : g_knownChars)
            HP_AddUniqueName(owners, n);
        for (const auto& kv : g_damageByAttacker) {
            if (HP_LooksLikePossessivePetName(kv.first)) HP_AddUniqueName(pets, kv.first);
            else if (LooksLikePcName(kv.first)) HP_AddUniqueName(owners, kv.first);
        }
    }

    {
        std::lock_guard<std::mutex> lk(g_liveDpsMutex);
        for (const auto& kv : g_liveDps.players) {
            if (HP_LooksLikePossessivePetName(kv.first)) HP_AddUniqueName(pets, kv.first);
            else HP_AddUniqueName(owners, kv.first);
        }
    }

    {
        std::lock_guard<std::mutex> lk(g_completedDpsMutex);
        for (const auto& fight : g_completedDpsFights) {
            for (const auto& kv : fight.players) {
                if (HP_LooksLikePossessivePetName(kv.first)) HP_AddUniqueName(pets, kv.first);
                else HP_AddUniqueName(owners, kv.first);
            }
        }
    }

    std::sort(pets.begin(), pets.end(), [](const std::string& a, const std::string& b) { return LowerCopy(a) < LowerCopy(b); });
    std::sort(owners.begin(), owners.end(), [](const std::string& a, const std::string& b) { return LowerCopy(a) < LowerCopy(b); });
}

static void HP_CopyStringToBuffer(char* dst, size_t dstSize, const std::string& src)
{
    if (!dst || dstSize == 0) return;
#ifdef _WIN32
    strncpy_s(dst, dstSize, src.c_str(), _TRUNCATE);
#else
    std::strncpy(dst, src.c_str(), dstSize - 1);
    dst[dstSize - 1] = '\0';
#endif
}


void AddLiveBurn(const std::string& who, const std::string& label, int seconds);

// ---------------------------------------------------------------------------
// Burn timer trigger rules.
// These watch MQ/EQ chat text for a user-supplied phrase and start/refresh the
// mini overlay Burn Timers view. Example: trigger text "Improved Twincast",
// display text "ITC", duration 120.
// ---------------------------------------------------------------------------
struct HP_BurnTriggerRule {
    std::string trigger;
    std::string display;
    int seconds = 60;
    bool enabled = true;
};

std::vector<HP_BurnTriggerRule> g_burnTriggerRules;
std::mutex g_burnTriggerRulesMutex;

static std::string HP_EscapeTsvField(const std::string& v)
{
    std::string out;
    out.reserve(v.size() + 8);
    for (char c : v) {
        if (c == '\\') out += "\\\\";
        else if (c == '\t') out += "\\t";
        else if (c == '\n') out += "\\n";
        else if (c == '\r') out += "\\r";
        else out.push_back(c);
    }
    return out;
}

static std::string HP_UnescapeTsvField(const std::string& v)
{
    std::string out;
    out.reserve(v.size());
    bool esc = false;
    for (char c : v) {
        if (esc) {
            if (c == 't') out.push_back('\t');
            else if (c == 'n') out.push_back('\n');
            else if (c == 'r') out.push_back('\r');
            else out.push_back(c);
            esc = false;
        } else if (c == '\\') esc = true;
        else out.push_back(c);
    }
    if (esc) out.push_back('\\');
    return out;
}

static void HP_SaveBurnTriggersUnlocked()
{
    std::ofstream out(kBurnTriggersFileName, std::ios::out | std::ios::trunc);
    if (!out.good()) return;
    out << "# HealParse Burn Timers v1\n";
    for (const auto& r : g_burnTriggerRules) {
        if (HP_TrimCopy(r.trigger).empty()) continue;
        out << (r.enabled ? 1 : 0) << '\t'
            << r.seconds << '\t'
            << HP_EscapeTsvField(r.trigger) << '\t'
            << HP_EscapeTsvField(r.display) << "\n";
    }
}

static void HP_SaveBurnTriggers()
{
    std::lock_guard<std::mutex> lk(g_burnTriggerRulesMutex);
    HP_SaveBurnTriggersUnlocked();
}

static void HP_LoadBurnTriggers()
{
    std::ifstream in(kBurnTriggersFileName);
    if (!in.good()) return;
    std::lock_guard<std::mutex> lk(g_burnTriggerRulesMutex);
    g_burnTriggerRules.clear();
    std::string line;
    while (std::getline(in, line)) {
        if (line.empty() || line[0] == '#') continue;
        std::vector<std::string> parts;
        size_t start = 0;
        while (true) {
            size_t tab = line.find('\t', start);
            if (tab == std::string::npos) { parts.push_back(line.substr(start)); break; }
            parts.push_back(line.substr(start, tab - start));
            start = tab + 1;
        }
        if (parts.size() < 3) continue;
        HP_BurnTriggerRule r;
        r.enabled = (atoi(parts[0].c_str()) != 0);
        r.seconds = std::max(1, atoi(parts[1].c_str()));
        r.trigger = HP_TrimCopy(HP_UnescapeTsvField(parts[2]));
        r.display = parts.size() >= 4 ? HP_TrimCopy(HP_UnescapeTsvField(parts[3])) : std::string();
        if (!r.trigger.empty()) g_burnTriggerRules.push_back(std::move(r));
    }
}

static void HP_SetBurnTriggerRule(const std::string& triggerText, const std::string& displayText, int seconds, bool enabled)
{
    std::string trigger = HP_TrimCopy(triggerText);
    std::string display = HP_TrimCopy(displayText);
    if (trigger.empty()) return;
    if (seconds < 1) seconds = 1;
    if (seconds > 36000) seconds = 36000;

    std::lock_guard<std::mutex> lk(g_burnTriggerRulesMutex);
    for (auto& r : g_burnTriggerRules) {
        if (LowerCopy(r.trigger) == LowerCopy(trigger)) {
            r.display = display;
            r.seconds = seconds;
            r.enabled = enabled;
            HP_SaveBurnTriggersUnlocked();
            return;
        }
    }
    HP_BurnTriggerRule r;
    r.trigger = trigger;
    r.display = display;
    r.seconds = seconds;
    r.enabled = enabled;
    g_burnTriggerRules.push_back(std::move(r));
    HP_SaveBurnTriggersUnlocked();
}

static std::vector<HP_BurnTriggerRule> HP_GetBurnTriggerRulesForUi()
{
    std::lock_guard<std::mutex> lk(g_burnTriggerRulesMutex);
    return g_burnTriggerRules;
}

static void HP_GetKnownSpellNamesForBurnPicker(std::vector<std::string>& out)
{
    out.clear();
    {
        std::lock_guard<std::mutex> lk(g_statsMutex);
        for (const auto& kv : g_spellCastsBySpell)
            HP_AddUniqueName(out, kv.first);
    }
    {
        std::lock_guard<std::mutex> lk(g_liveDpsMutex);
        for (const auto& kv : g_liveDps.spellCasts)
            HP_AddUniqueName(out, kv.first);
    }
    {
        std::lock_guard<std::mutex> lk(g_completedDpsMutex);
        for (const auto& f : g_completedDpsFights)
            for (const auto& kv : f.spellCasts)
                HP_AddUniqueName(out, kv.first);
    }
    std::sort(out.begin(), out.end(), [](const std::string& a, const std::string& b) { return LowerCopy(a) < LowerCopy(b); });
}

static std::string HP_RemoveMqColorCodes(std::string s)
{
    std::string out;
    out.reserve(s.size());

    // MQ color codes can arrive as \aw, \ax, \ag, or the longer form
    // \a-w / \a-x / \a-g depending on the chat path.  The previous stripper
    // removed only "\a-" and left the color letter behind, producing text like
    // "E3]-w <Eyehop>".  That made the burn owner parser pick the wrong token.
    for (size_t i = 0; i < s.size(); ++i) {
        unsigned char c = (unsigned char)s[i];

        if (s[i] == '\\' && i + 1 < s.size() && s[i + 1] == 'a') {
            i += 2; // consumed backslash + a
            if (i < s.size() && s[i] == '-')
                ++i; // optional dash in \a-w style codes
            // consume the color code character if one exists (w/x/g/y/r/etc.)
            // The for-loop increment will move to the next real text char.
            continue;
        }

        // Some MQ builds pass the color escape as a single control byte followed
        // by the color char. Drop the control byte and the optional code char.
        if (c < 32 && c != '\t') {
            if (i + 1 < s.size() && (std::isalpha((unsigned char)s[i + 1]) || s[i + 1] == '-')) {
                if (s[i + 1] == '-' && i + 2 < s.size()) i += 2;
                else i += 1;
            }
            continue;
        }

        out.push_back(s[i]);
    }
    return out;
}

static std::string HP_CleanPossibleNameToken(std::string tok)
{
    tok = HP_RemoveMqColorCodes(HP_TrimCopy(tok));

    size_t lb = tok.find('<');
    size_t rb = (lb == std::string::npos) ? std::string::npos : tok.find('>', lb + 1);
    if (lb != std::string::npos && rb != std::string::npos && rb > lb + 1)
        tok = tok.substr(lb + 1, rb - lb - 1);

    tok = HP_TrimCopy(tok);
    while (!tok.empty() && (tok.front() == '<' || tok.front() == '[' || tok.front() == '(' || tok.front() == ':' || tok.front() == ',' || tok.front() == '\'' || tok.front() == '"'))
        tok.erase(tok.begin());
    while (!tok.empty() && (tok.back() == '>' || tok.back() == ']' || tok.back() == ')' || tok.back() == ':' || tok.back() == ',' || tok.back() == '\'' || tok.back() == '"'))
        tok.pop_back();

    tok = HP_TrimCopy(tok);
    while (!tok.empty() && !std::isalpha((unsigned char)tok.front())) tok.erase(tok.begin());
    while (!tok.empty() && !std::isalpha((unsigned char)tok.back())) tok.pop_back();
    return HP_TrimCopy(tok);
}

static std::string HP_ExtractBurnSpeakerName(const char* line, const std::string& myName)
{
    if (!line) return myName.empty() ? std::string("Unknown") : myName;
    std::string s = HP_RemoveMqColorCodes(HP_TrimCopy(line));
    if (s.empty()) return myName.empty() ? std::string("Unknown") : myName;

    if (IStartsWith(s.c_str(), "You ") || IStartsWith(s.c_str(), "Your "))
        return myName.empty() ? std::string("You") : myName;

    // Remove leading MQ/E3 channel prefix, but keep the rest of the line.
    // Examples:
    //   [E3]10:08:22 <Eyehop> Epic: Staff of Ancient Power Rk. II
    //   [MQ2] <Dorias> Long Burn: Improved Twincast
    if (!s.empty() && s[0] == '[') {
        size_t rb = s.find(']');
        if (rb != std::string::npos && rb + 1 < s.size())
            s = HP_TrimCopy(s.substr(rb + 1));
    }

    // Strip a leading clock timestamp after the MQ/E3 prefix.
    // This was the reason lines like "[E3]10:08:22 <Eyehop> Epic: ..."
    // were attaching the timer to the burn name instead of the player.
    if (s.size() >= 8 &&
        isdigit((unsigned char)s[0]) && isdigit((unsigned char)s[1]) && s[2] == ':' &&
        isdigit((unsigned char)s[3]) && isdigit((unsigned char)s[4]) && s[5] == ':' &&
        isdigit((unsigned char)s[6]) && isdigit((unsigned char)s[7])) {
        s = HP_TrimCopy(s.substr(8));
    }

    // Prefer ANY <Player> token anywhere in the MQ/E3 line. Do this before
    // colon parsing, because E3 lines often start with a timestamp containing
    // colons before the real player token.
    size_t angleSearch = 0;
    while (true) {
        size_t lb = s.find('<', angleSearch);
        if (lb == std::string::npos) break;
        size_t rb = s.find('>', lb + 1);
        if (rb == std::string::npos) break;
        std::string who = HP_CleanPossibleNameToken(s.substr(lb + 1, rb - lb - 1));
        if (LooksLikePcName(who)) return who;
        angleSearch = rb + 1;
    }

    // E3 relay form: "Dorfus => Dorias : /nowcast ...". The timer belongs to
    // the target toon after the arrow, not the relay sender.
    size_t arrow = s.find("=>");
    if (arrow != std::string::npos) {
        size_t a = arrow + 2;
        size_t b = s.find(':', a);
        std::string who = HP_CleanPossibleNameToken(s.substr(a, b == std::string::npos ? std::string::npos : b - a));
        if (LooksLikePcName(who)) return who;
    }

    // Common chat/relay forms: "Dorias: Epic ...", "Dorias - Epic ...".
    for (const char* sep : { " - ", " says", " tells", " auctions", " shouts", " ooc", ":" }) {
        size_t p = s.find(sep);
        if (p != std::string::npos && p > 0) {
            std::string who = HP_CleanPossibleNameToken(s.substr(0, p));
            if (LooksLikePcName(who)) return who;
        }
    }

    const char* cuts[] = { " begins ", " is ", " has ", " hit ", " hits ", " strikes ", " casts " };
    size_t best = std::string::npos;
    for (const char* c : cuts) {
        size_t p = s.find(c);
        if (p != std::string::npos && p < best) best = p;
    }
    if (best != std::string::npos && best > 0) {
        std::string who = HP_CleanPossibleNameToken(s.substr(0, best));
        if (LooksLikePcName(who)) return who;
    }

    // Fallback to the first cleaned PC-looking token in the line.
    std::istringstream iss(s);
    std::string tok;
    while (iss >> tok) {
        std::string who = HP_CleanPossibleNameToken(tok);
        if (LooksLikePcName(who)) return who;
    }
    return myName.empty() ? std::string("Unknown") : myName;
}

static void HP_CheckBurnTriggers(const char* line, const std::string& myName)
{
    if (!line || !*line) return;
    std::vector<HP_BurnTriggerRule> rules;
    {
        std::lock_guard<std::mutex> lk(g_burnTriggerRulesMutex);
        rules = g_burnTriggerRules;
    }
    if (rules.empty()) return;

    std::string lowerLine = LowerCopy(line);
    for (const auto& r : rules) {
        if (!r.enabled || r.trigger.empty() || r.seconds <= 0) continue;
        if (lowerLine.find(LowerCopy(r.trigger)) == std::string::npos) continue;
        std::string who = HP_ExtractBurnSpeakerName(line, myName);
        std::string label = HP_TrimCopy(r.display.empty() ? r.trigger : r.display);

        // Do not allow the trigger/item text to become the player name. If the
        // speaker could not be found from <Player> / E3 relay formats, fall back
        // to the local character rather than showing "Staff - Epic".
        std::string firstTriggerWord;
        {
            std::istringstream iss(r.trigger);
            iss >> firstTriggerWord;
        }
        if (who.empty() || !LooksLikePcName(who) || (!firstTriggerWord.empty() && HP_SameNameNoCase(who, firstTriggerWord)))
            who = myName.empty() ? std::string("Unknown") : myName;

        AddLiveBurn(who, label, r.seconds);
        // Do NOT force-open or auto-switch the mini overlay from burn triggers.
        // Burn timers continue running in the background, but the live mini tracker
        // stays on whatever view the user selected until they manually switch it.
        break; // one line should not start multiple timers accidentally
    }
}

// Plugin-owned after-fight popup.  This mirrors the old Lua after-fight mini
// summary, but it is drawn directly by the plugin so it does not depend on Lua.
CompletedDpsFight g_afterFightPopup;
std::mutex g_afterFightPopupMutex;
std::atomic<bool> g_afterFightPopupOpen{ false };
std::atomic<int64_t> g_afterFightPopupShownMs{ 0 };
std::atomic<int> g_afterFightPopupLingerSec{ 12 };
std::atomic<bool> g_enableAfterFightPopup{ true };


// ----------------------------------------------------------------------------
// Fight-list mob icon texture support
// ----------------------------------------------------------------------------
// Put your PNG here, next to the compiled plugin DLL:
//   MQ2HealParse\Images\Demon.png
//
// The loader is intentionally plugin-side so you can swap the PNG without
// changing Lua or recompiling. It tries to load using the active Dear ImGui
// DX11 renderer device. If texture loading fails, the UI falls back to a small
// drawn red icon instead of breaking the fight list.
struct HP_IconTexture {
    ImTextureID id = nullptr;
    int width = 0;
    int height = 0;
    bool attempted = false;
    std::string loadedPath;
};

static HP_IconTexture g_demonIconTexture;
static HP_IconTexture g_swordsIconTexture;
static HP_IconTexture g_healsIconTexture;
static HP_IconTexture g_dpsIconTexture;
static HP_IconTexture g_deathsIconTexture;
static HP_IconTexture g_playersIconTexture;
static HP_IconTexture g_durationIconTexture;
static HP_IconTexture g_spellsIconTexture;
static HP_IconTexture g_tankIconTexture;
static HP_IconTexture g_historyIconTexture;
static HP_IconTexture g_settingsIconTexture;
static HP_IconTexture g_healtrackerLogoTexture;
static HP_IconTexture g_ghostIconTexture;
static HP_IconTexture g_refreshIconTexture;
static HP_IconTexture g_calIconTexture;
static HP_IconTexture g_wizIconTexture;
static HP_IconTexture g_encIconTexture;
static HP_IconTexture g_clerIconTexture;
static HP_IconTexture g_necIconTexture;
static HP_IconTexture g_mageIconTexture;
static HP_IconTexture g_palIconTexture;
static HP_IconTexture g_bstIconTexture;
static HP_IconTexture g_rngIconTexture;
static HP_IconTexture g_brdIconTexture;
static HP_IconTexture g_berIconTexture;
static HP_IconTexture g_druIconTexture;
static HP_IconTexture g_mnkIconTexture;
static HP_IconTexture g_rogIconTexture;
static HP_IconTexture g_skIconTexture;
static HP_IconTexture g_shmIconTexture;
static HP_IconTexture g_warIconTexture;

struct HP_MobIconTextureEntry {
    HP_IconTexture tex;
#ifdef _WIN32
    ID3D11ShaderResourceView* srv = nullptr;
    IDirect3DTexture9* tex9 = nullptr;
#endif
};
static std::unordered_map<std::string, HP_MobIconTextureEntry> g_mobIconTextures;

// Prevent mob portrait PNG discovery/loading from causing a one-frame hitch
// when a fight is archived and the fight list/popup redraws. Missing PNGs can
// require several file checks, so spread those attempts across frames.
static int g_mobIconTextureLoadFrame = -1;
static int g_mobIconTextureLoadsThisFrame = 0;
constexpr int kMaxMobIconTextureLoadsPerFrame = 1;


#ifdef _WIN32
static ID3D11ShaderResourceView* g_demonIconSrv = nullptr;
static IDirect3DTexture9* g_demonIconTex9 = nullptr;
static ID3D11ShaderResourceView* g_swordsIconSrv = nullptr;
static IDirect3DTexture9* g_swordsIconTex9 = nullptr;
static ID3D11ShaderResourceView* g_healtrackerLogoSrv = nullptr;
static IDirect3DTexture9* g_healtrackerLogoTex9 = nullptr;
static ID3D11ShaderResourceView* g_healsIconSrv = nullptr;
static IDirect3DTexture9* g_healsIconTex9 = nullptr;
static ID3D11ShaderResourceView* g_dpsIconSrv = nullptr;
static IDirect3DTexture9* g_dpsIconTex9 = nullptr;
static ID3D11ShaderResourceView* g_deathsIconSrv = nullptr;
static IDirect3DTexture9* g_deathsIconTex9 = nullptr;
static ID3D11ShaderResourceView* g_playersIconSrv = nullptr;
static IDirect3DTexture9* g_playersIconTex9 = nullptr;
static ID3D11ShaderResourceView* g_durationIconSrv = nullptr;
static IDirect3DTexture9* g_durationIconTex9 = nullptr;
static ID3D11ShaderResourceView* g_spellsIconSrv = nullptr;
static IDirect3DTexture9* g_spellsIconTex9 = nullptr;
static ID3D11ShaderResourceView* g_tankIconSrv = nullptr;
static IDirect3DTexture9* g_tankIconTex9 = nullptr;
static ID3D11ShaderResourceView* g_historyIconSrv = nullptr;
static IDirect3DTexture9* g_historyIconTex9 = nullptr;
static ID3D11ShaderResourceView* g_settingsIconSrv = nullptr;
static IDirect3DTexture9* g_settingsIconTex9 = nullptr;
static ID3D11ShaderResourceView* g_ghostIconSrv = nullptr;
static IDirect3DTexture9* g_ghostIconTex9 = nullptr;
static ID3D11ShaderResourceView* g_refreshIconSrv = nullptr;
static IDirect3DTexture9* g_refreshIconTex9 = nullptr;
static ID3D11ShaderResourceView* g_calIconSrv = nullptr;
static IDirect3DTexture9* g_calIconTex9 = nullptr;
static ID3D11ShaderResourceView* g_wizIconSrv = nullptr;
static IDirect3DTexture9* g_wizIconTex9 = nullptr;
static ID3D11ShaderResourceView* g_encIconSrv = nullptr;
static IDirect3DTexture9* g_encIconTex9 = nullptr;
static ID3D11ShaderResourceView* g_clerIconSrv = nullptr;
static IDirect3DTexture9* g_clerIconTex9 = nullptr;
static ID3D11ShaderResourceView* g_necIconSrv = nullptr;
static IDirect3DTexture9* g_necIconTex9 = nullptr;
static ID3D11ShaderResourceView* g_mageIconSrv = nullptr;
static IDirect3DTexture9* g_mageIconTex9 = nullptr;
static ID3D11ShaderResourceView* g_palIconSrv = nullptr;
static IDirect3DTexture9* g_palIconTex9 = nullptr;
static ID3D11ShaderResourceView* g_bstIconSrv = nullptr;
static IDirect3DTexture9* g_bstIconTex9 = nullptr;
static ID3D11ShaderResourceView* g_rngIconSrv = nullptr;
static IDirect3DTexture9* g_rngIconTex9 = nullptr;
static ID3D11ShaderResourceView* g_brdIconSrv = nullptr;
static IDirect3DTexture9* g_brdIconTex9 = nullptr;
static ID3D11ShaderResourceView* g_berIconSrv = nullptr;
static IDirect3DTexture9* g_berIconTex9 = nullptr;
static ID3D11ShaderResourceView* g_druIconSrv = nullptr;
static IDirect3DTexture9* g_druIconTex9 = nullptr;
static ID3D11ShaderResourceView* g_mnkIconSrv = nullptr;
static IDirect3DTexture9* g_mnkIconTex9 = nullptr;
static ID3D11ShaderResourceView* g_rogIconSrv = nullptr;
static IDirect3DTexture9* g_rogIconTex9 = nullptr;
static ID3D11ShaderResourceView* g_skIconSrv = nullptr;
static IDirect3DTexture9* g_skIconTex9 = nullptr;
static ID3D11ShaderResourceView* g_shmIconSrv = nullptr;
static IDirect3DTexture9* g_shmIconTex9 = nullptr;
static ID3D11ShaderResourceView* g_warIconSrv = nullptr;
static IDirect3DTexture9* g_warIconTex9 = nullptr;

struct HP_ImGuiDx11BackendData {
    ID3D11Device* pd3dDevice;
    ID3D11DeviceContext* pd3dDeviceContext;
    IDXGIFactory* pFactory;
};

static bool HP_FileExistsA(const std::string& path)
{
    DWORD attr = GetFileAttributesA(path.c_str());
    return attr != INVALID_FILE_ATTRIBUTES && !(attr & FILE_ATTRIBUTE_DIRECTORY);
}

static std::string HP_DirNameA(const std::string& path)
{
    size_t p = path.find_last_of("\\/");
    if (p == std::string::npos) return std::string();
    return path.substr(0, p);
}

static std::vector<std::string> HP_GetDemonIconCandidatePaths()
{
    std::vector<std::string> paths;

    char dllPath[MAX_PATH] = { 0 };
    HMODULE hMod = nullptr;
    GetModuleHandleExA(GET_MODULE_HANDLE_EX_FLAG_FROM_ADDRESS | GET_MODULE_HANDLE_EX_FLAG_UNCHANGED_REFCOUNT,
        reinterpret_cast<LPCSTR>(&HP_FileExistsA), &hMod);
    if (!hMod) hMod = GetModuleHandleA("MQ2HealParse.dll");
    if (!hMod) hMod = GetModuleHandleA("MQ2HealParse_Test.dll");
    if (hMod && GetModuleFileNameA(hMod, dllPath, MAX_PATH) > 0) {
        std::string dir = HP_DirNameA(dllPath);
        if (!dir.empty()) {
            // Most MQ installs put the DLL directly in <MQ>\plugins, while
            // plugin-specific assets live under <MQ>\plugins\MQ2HealParse\Images.
            paths.push_back(dir + "\\MQ2HealParse\\Images\\Demon.png");
            paths.push_back(dir + "\\MQ2HealParseImages\\Demon.png");
            paths.push_back(dir + "\\Images\\Demon.png");
            paths.push_back(dir + "\\Demon.png");
        }
    }

    if (gPathMQRoot && gPathMQRoot[0]) {
        std::string root = gPathMQRoot;
        paths.push_back(root + "\\plugins\\MQ2HealParse\\Images\\Demon.png");
        paths.push_back(root + "\\plugins\\MQ2HealParseImages\\Demon.png");
        paths.push_back(root + "\\MQ2HealParseImages\\Demon.png");
        paths.push_back(root + "\\Images\\Demon.png");
        paths.push_back(root + "\\plugins\\Images\\Demon.png");
    }

    paths.push_back("Images\\Demon.png");
    paths.push_back(".\\Images\\Demon.png");
    paths.push_back("MQ2HealParseImages\\Demon.png");
    paths.push_back(".\\MQ2HealParseImages\\Demon.png");
    paths.push_back("plugins\\MQ2HealParse\\Images\\Demon.png");
    paths.push_back("plugins\\MQ2HealParseImages\\Demon.png");
    paths.push_back("MQ2HealParse\\Images\\Demon.png");
    return paths;
}

static std::vector<std::string> HP_GetImageCandidatePaths(const char* fileName)
{
    std::vector<std::string> paths;
    if (!fileName || !fileName[0]) return paths;

    char dllPath[MAX_PATH] = { 0 };
    HMODULE hMod = nullptr;
    GetModuleHandleExA(GET_MODULE_HANDLE_EX_FLAG_FROM_ADDRESS | GET_MODULE_HANDLE_EX_FLAG_UNCHANGED_REFCOUNT,
        reinterpret_cast<LPCSTR>(&HP_FileExistsA), &hMod);
    if (!hMod) hMod = GetModuleHandleA("MQ2HealParse.dll");
    if (!hMod) hMod = GetModuleHandleA("MQ2HealParse_Test.dll");
    if (hMod && GetModuleFileNameA(hMod, dllPath, MAX_PATH) > 0) {
        std::string dir = HP_DirNameA(dllPath);
        if (!dir.empty()) {
            paths.push_back(dir + "\\MQ2HealParse\\Images\\" + fileName);
            paths.push_back(dir + "\\MQ2HealParseImages\\" + fileName);
            paths.push_back(dir + "\\Images\\" + fileName);
            paths.push_back(dir + "\\" + fileName);
        }
    }

    if (gPathMQRoot && gPathMQRoot[0]) {
        std::string root = gPathMQRoot;
        paths.push_back(root + "\\plugins\\MQ2HealParse\\Images\\" + fileName);
        paths.push_back(root + "\\Plugins\\MQ2HealParse\\Images\\" + fileName);
        paths.push_back(root + "\\plugins\\MQ2HealParseImages\\" + fileName);
        paths.push_back(root + "\\Plugins\\MQ2HealParseImages\\" + fileName);
        paths.push_back(root + "\\MQ2HealParseImages\\" + fileName);
        paths.push_back(root + "\\Images\\" + fileName);
        paths.push_back(root + "\\plugins\\Images\\" + fileName);
        paths.push_back(root + "\\plugins\\" + fileName);
    }

    paths.push_back(std::string("Images\\") + fileName);
    paths.push_back(std::string(".\\Images\\") + fileName);
    paths.push_back(std::string("MQ2HealParseImages\\") + fileName);
    paths.push_back(std::string(".\\MQ2HealParseImages\\") + fileName);
    paths.push_back(std::string("plugins\\MQ2HealParse\\Images\\") + fileName);
    paths.push_back(std::string("plugins\\MQ2HealParseImages\\") + fileName);
    paths.push_back(std::string("MQ2HealParse\\Images\\") + fileName);
    return paths;
}

static std::wstring HP_ToWide(const std::string& s)
{
    if (s.empty()) return std::wstring();
    int n = MultiByteToWideChar(CP_UTF8, 0, s.c_str(), -1, nullptr, 0);
    if (n <= 0) n = MultiByteToWideChar(CP_ACP, 0, s.c_str(), -1, nullptr, 0);
    if (n <= 0) return std::wstring();
    std::wstring w((size_t)n, L'\0');
    if (MultiByteToWideChar(CP_UTF8, 0, s.c_str(), -1, &w[0], n) <= 0)
        MultiByteToWideChar(CP_ACP, 0, s.c_str(), -1, &w[0], n);
    if (!w.empty() && w.back() == L'\0') w.pop_back();
    return w;
}

static ID3D11Device* HP_GetImGuiDx11Device()
{
    ImGuiIO& io = ImGui::GetIO();
    if (!io.BackendRendererUserData) return nullptr;
    if (!io.BackendRendererName || strstr(io.BackendRendererName, "DX11") == nullptr)
        return nullptr;

    HP_ImGuiDx11BackendData* bd = reinterpret_cast<HP_ImGuiDx11BackendData*>(io.BackendRendererUserData);
    return bd ? bd->pd3dDevice : nullptr;
}


struct HP_ImGuiDx9BackendData {
    IDirect3DDevice9* pd3dDevice;
};

static IDirect3DDevice9* HP_GetImGuiDx9Device()
{
    ImGuiIO& io = ImGui::GetIO();
    if (!io.BackendRendererUserData) return nullptr;
    if (!io.BackendRendererName || (strstr(io.BackendRendererName, "DX9") == nullptr && strstr(io.BackendRendererName, "dx9") == nullptr))
        return nullptr;

    HP_ImGuiDx9BackendData* bd = reinterpret_cast<HP_ImGuiDx9BackendData*>(io.BackendRendererUserData);
    return bd ? bd->pd3dDevice : nullptr;
}

static bool HP_DecodePngBGRA(const std::string& path, std::vector<unsigned char>& pixels, int* outW, int* outH)
{
    if (!outW || !outH) return false;
    *outW = *outH = 0;
    pixels.clear();

    HRESULT hrCo = CoInitializeEx(nullptr, COINIT_MULTITHREADED);
    (void)hrCo;

    IWICImagingFactory* factory = nullptr;
    HRESULT hr = CoCreateInstance(CLSID_WICImagingFactory, nullptr, CLSCTX_INPROC_SERVER,
        IID_PPV_ARGS(&factory));
    if (FAILED(hr) || !factory) return false;

    IWICBitmapDecoder* decoder = nullptr;
    std::wstring wpath = HP_ToWide(path);
    hr = factory->CreateDecoderFromFilename(wpath.c_str(), nullptr, GENERIC_READ,
        WICDecodeMetadataCacheOnLoad, &decoder);
    if (FAILED(hr) || !decoder) { factory->Release(); return false; }

    IWICBitmapFrameDecode* frame = nullptr;
    hr = decoder->GetFrame(0, &frame);
    if (FAILED(hr) || !frame) { decoder->Release(); factory->Release(); return false; }

    IWICFormatConverter* converter = nullptr;
    hr = factory->CreateFormatConverter(&converter);
    if (FAILED(hr) || !converter) { frame->Release(); decoder->Release(); factory->Release(); return false; }

    // BGRA works for both D3D9 A8R8G8B8 and D3D11 B8G8R8A8.
    hr = converter->Initialize(frame, GUID_WICPixelFormat32bppBGRA,
        WICBitmapDitherTypeNone, nullptr, 0.0, WICBitmapPaletteTypeCustom);
    if (FAILED(hr)) { converter->Release(); frame->Release(); decoder->Release(); factory->Release(); return false; }

    UINT width = 0, height = 0;
    converter->GetSize(&width, &height);
    if (width == 0 || height == 0) { converter->Release(); frame->Release(); decoder->Release(); factory->Release(); return false; }

    pixels.resize((size_t)width * (size_t)height * 4u);
    hr = converter->CopyPixels(nullptr, width * 4u, (UINT)pixels.size(), pixels.data());

    converter->Release();
    frame->Release();
    decoder->Release();
    factory->Release();

    if (FAILED(hr)) { pixels.clear(); return false; }
    *outW = (int)width;
    *outH = (int)height;
    return true;
}

static bool HP_LoadPngTextureDx9(const std::string& path, IDirect3DTexture9** outTex, int* outW, int* outH)
{
    if (!outTex || !outW || !outH) return false;
    *outTex = nullptr;
    *outW = *outH = 0;

    IDirect3DDevice9* device = HP_GetImGuiDx9Device();
    if (!device) return false;

    std::vector<unsigned char> pixels;
    int width = 0, height = 0;
    if (!HP_DecodePngBGRA(path, pixels, &width, &height)) return false;

    IDirect3DTexture9* tex = nullptr;
    HRESULT hr = device->CreateTexture((UINT)width, (UINT)height, 1, D3DUSAGE_DYNAMIC,
        D3DFMT_A8R8G8B8, D3DPOOL_DEFAULT, &tex, nullptr);
    if (FAILED(hr) || !tex) return false;

    D3DLOCKED_RECT rect{};
    hr = tex->LockRect(0, &rect, nullptr, D3DLOCK_DISCARD);
    if (FAILED(hr)) { tex->Release(); return false; }

    for (int y = 0; y < height; ++y) {
        memcpy((unsigned char*)rect.pBits + (size_t)y * rect.Pitch,
            pixels.data() + (size_t)y * width * 4u,
            (size_t)width * 4u);
    }
    tex->UnlockRect(0);

    *outTex = tex;
    *outW = width;
    *outH = height;
    return true;
}

static bool HP_LoadPngTextureDx11(const std::string& path, ID3D11ShaderResourceView** outSrv, int* outW, int* outH)
{
    if (!outSrv || !outW || !outH) return false;
    *outSrv = nullptr;
    *outW = *outH = 0;

    ID3D11Device* device = HP_GetImGuiDx11Device();
    if (!device) return false;

    HRESULT hrCo = CoInitializeEx(nullptr, COINIT_MULTITHREADED);
    (void)hrCo; // S_OK, S_FALSE, and RPC_E_CHANGED_MODE are all safe here.

    IWICImagingFactory* factory = nullptr;
    HRESULT hr = CoCreateInstance(CLSID_WICImagingFactory, nullptr, CLSCTX_INPROC_SERVER,
        IID_PPV_ARGS(&factory));
    if (FAILED(hr) || !factory) return false;

    IWICBitmapDecoder* decoder = nullptr;
    std::wstring wpath = HP_ToWide(path);
    hr = factory->CreateDecoderFromFilename(wpath.c_str(), nullptr, GENERIC_READ,
        WICDecodeMetadataCacheOnLoad, &decoder);
    if (FAILED(hr) || !decoder) { factory->Release(); return false; }

    IWICBitmapFrameDecode* frame = nullptr;
    hr = decoder->GetFrame(0, &frame);
    if (FAILED(hr) || !frame) { decoder->Release(); factory->Release(); return false; }

    IWICFormatConverter* converter = nullptr;
    hr = factory->CreateFormatConverter(&converter);
    if (FAILED(hr) || !converter) { frame->Release(); decoder->Release(); factory->Release(); return false; }

    hr = converter->Initialize(frame, GUID_WICPixelFormat32bppRGBA,
        WICBitmapDitherTypeNone, nullptr, 0.0, WICBitmapPaletteTypeCustom);
    if (FAILED(hr)) { converter->Release(); frame->Release(); decoder->Release(); factory->Release(); return false; }

    UINT width = 0, height = 0;
    converter->GetSize(&width, &height);
    if (width == 0 || height == 0) { converter->Release(); frame->Release(); decoder->Release(); factory->Release(); return false; }

    std::vector<unsigned char> pixels((size_t)width * (size_t)height * 4u);
    hr = converter->CopyPixels(nullptr, width * 4u, (UINT)pixels.size(), pixels.data());
    if (FAILED(hr)) { converter->Release(); frame->Release(); decoder->Release(); factory->Release(); return false; }

    D3D11_TEXTURE2D_DESC desc{};
    desc.Width = width;
    desc.Height = height;
    desc.MipLevels = 1;
    desc.ArraySize = 1;
    desc.Format = DXGI_FORMAT_R8G8B8A8_UNORM;
    desc.SampleDesc.Count = 1;
    desc.Usage = D3D11_USAGE_DEFAULT;
    desc.BindFlags = D3D11_BIND_SHADER_RESOURCE;

    D3D11_SUBRESOURCE_DATA initData{};
    initData.pSysMem = pixels.data();
    initData.SysMemPitch = width * 4u;

    ID3D11Texture2D* texture = nullptr;
    hr = device->CreateTexture2D(&desc, &initData, &texture);
    if (FAILED(hr) || !texture) { converter->Release(); frame->Release(); decoder->Release(); factory->Release(); return false; }

    D3D11_SHADER_RESOURCE_VIEW_DESC srvDesc{};
    srvDesc.Format = desc.Format;
    srvDesc.ViewDimension = D3D11_SRV_DIMENSION_TEXTURE2D;
    srvDesc.Texture2D.MipLevels = 1;

    hr = device->CreateShaderResourceView(texture, &srvDesc, outSrv);
    texture->Release();

    converter->Release();
    frame->Release();
    decoder->Release();
    factory->Release();

    if (FAILED(hr) || !*outSrv) return false;
    *outW = (int)width;
    *outH = (int)height;
    return true;
}
#endif

static void HP_LoadDemonIconTextureIfNeeded()
{
    if (g_demonIconTexture.attempted) return;
    g_demonIconTexture.attempted = true;

#ifdef _WIN32
    for (const std::string& path : HP_GetDemonIconCandidatePaths()) {
        if (!HP_FileExistsA(path)) continue;
        int w = 0, h = 0;
        ID3D11ShaderResourceView* srv = nullptr;
        if (HP_LoadPngTextureDx11(path, &srv, &w, &h)) {
            g_demonIconSrv = srv;
            g_demonIconTexture.id = reinterpret_cast<ImTextureID>(srv);
            g_demonIconTexture.width = w;
            g_demonIconTexture.height = h;
            g_demonIconTexture.loadedPath = path;
            return;
        }

        IDirect3DTexture9* tex9 = nullptr;
        if (HP_LoadPngTextureDx9(path, &tex9, &w, &h)) {
            g_demonIconTex9 = tex9;
            g_demonIconTexture.id = reinterpret_cast<ImTextureID>(tex9);
            g_demonIconTexture.width = w;
            g_demonIconTexture.height = h;
            g_demonIconTexture.loadedPath = path;
            return;
        }
    }
#endif
}

static void HP_LoadSwordsIconTextureIfNeeded()
{
    if (g_swordsIconTexture.attempted) return;
    g_swordsIconTexture.attempted = true;

#ifdef _WIN32
    std::vector<std::string> candidates = HP_GetImageCandidatePaths("Swords.png");
    std::vector<std::string> noExt = HP_GetImageCandidatePaths("Swords");
    candidates.insert(candidates.end(), noExt.begin(), noExt.end());

    for (const std::string& path : candidates) {
        if (!HP_FileExistsA(path)) continue;
        int w = 0, h = 0;
        ID3D11ShaderResourceView* srv = nullptr;
        if (HP_LoadPngTextureDx11(path, &srv, &w, &h)) {
            g_swordsIconSrv = srv;
            g_swordsIconTexture.id = reinterpret_cast<ImTextureID>(srv);
            g_swordsIconTexture.width = w;
            g_swordsIconTexture.height = h;
            g_swordsIconTexture.loadedPath = path;
            return;
        }

        IDirect3DTexture9* tex9 = nullptr;
        if (HP_LoadPngTextureDx9(path, &tex9, &w, &h)) {
            g_swordsIconTex9 = tex9;
            g_swordsIconTexture.id = reinterpret_cast<ImTextureID>(tex9);
            g_swordsIconTexture.width = w;
            g_swordsIconTexture.height = h;
            g_swordsIconTexture.loadedPath = path;
            return;
        }
    }
#endif
}


static void HP_LoadNamedIconTextureIfNeeded(HP_IconTexture& tex, ID3D11ShaderResourceView*& srvOut, IDirect3DTexture9*& tex9Out, const char* fileName, const char* label)
{
    if (tex.attempted) return;
    tex.attempted = true;

#ifdef _WIN32
    std::vector<std::string> candidates = HP_GetImageCandidatePaths(fileName);
    for (const std::string& path : candidates) {
        if (!HP_FileExistsA(path)) continue;
        int w = 0, h = 0;
        ID3D11ShaderResourceView* srv = nullptr;
        if (HP_LoadPngTextureDx11(path, &srv, &w, &h)) {
            srvOut = srv;
            tex.id = reinterpret_cast<ImTextureID>(srv);
            tex.width = w;
            tex.height = h;
            tex.loadedPath = path;
            return;
        }

        IDirect3DTexture9* tex9 = nullptr;
        if (HP_LoadPngTextureDx9(path, &tex9, &w, &h)) {
            tex9Out = tex9;
            tex.id = reinterpret_cast<ImTextureID>(tex9);
            tex.width = w;
            tex.height = h;
            tex.loadedPath = path;
            return;
        }
    }
#endif
}

static void HP_LoadHealtrackerLogoTextureIfNeeded()
{
    // User-provided UI banner/logo. Put it in:
    //   MQ2HealParse\Images\Healtracker.png
    // The loader also checks "Healtracker" without extension for consistency
    // with the other image loaders.
    if (g_healtrackerLogoTexture.attempted) return;
    g_healtrackerLogoTexture.attempted = true;

#ifdef _WIN32
    std::vector<std::string> candidates = HP_GetImageCandidatePaths("Healtracker.png");
    std::vector<std::string> noExt = HP_GetImageCandidatePaths("Healtracker");
    candidates.insert(candidates.end(), noExt.begin(), noExt.end());

    for (const std::string& path : candidates) {
        if (!HP_FileExistsA(path)) continue;
        int w = 0, h = 0;
        ID3D11ShaderResourceView* srv = nullptr;
        if (HP_LoadPngTextureDx11(path, &srv, &w, &h)) {
            g_healtrackerLogoSrv = srv;
            g_healtrackerLogoTexture.id = reinterpret_cast<ImTextureID>(srv);
            g_healtrackerLogoTexture.width = w;
            g_healtrackerLogoTexture.height = h;
            g_healtrackerLogoTexture.loadedPath = path;
            return;
        }

        IDirect3DTexture9* tex9 = nullptr;
        if (HP_LoadPngTextureDx9(path, &tex9, &w, &h)) {
            g_healtrackerLogoTex9 = tex9;
            g_healtrackerLogoTexture.id = reinterpret_cast<ImTextureID>(tex9);
            g_healtrackerLogoTexture.width = w;
            g_healtrackerLogoTexture.height = h;
            g_healtrackerLogoTexture.loadedPath = path;
            return;
        }
    }
#endif
}

static void HP_LoadHealsIconTextureIfNeeded()
{
    HP_LoadNamedIconTextureIfNeeded(g_healsIconTexture, g_healsIconSrv, g_healsIconTex9, "Heals.png", "Heals icon");
}

static void HP_LoadDpsIconTextureIfNeeded()
{
    HP_LoadNamedIconTextureIfNeeded(g_dpsIconTexture, g_dpsIconSrv, g_dpsIconTex9, "DPS.png", "DPS icon");
}

static void HP_LoadDeathsIconTextureIfNeeded()
{
    HP_LoadNamedIconTextureIfNeeded(g_deathsIconTexture, g_deathsIconSrv, g_deathsIconTex9, "Deaths.png", "Deaths icon");
}

static void HP_LoadPlayersIconTextureIfNeeded()
{
    HP_LoadNamedIconTextureIfNeeded(g_playersIconTexture, g_playersIconSrv, g_playersIconTex9, "Players.png", "Players icon");
}

static void HP_LoadDurationIconTextureIfNeeded()
{
    HP_LoadNamedIconTextureIfNeeded(g_durationIconTexture, g_durationIconSrv, g_durationIconTex9, "Duration.png", "Duration icon");
}

static void HP_LoadSpellsIconTextureIfNeeded()
{
    HP_LoadNamedIconTextureIfNeeded(g_spellsIconTexture, g_spellsIconSrv, g_spellsIconTex9, "Spells.png", "Spells icon");
}

static void HP_LoadTankIconTextureIfNeeded()
{
    HP_LoadNamedIconTextureIfNeeded(g_tankIconTexture, g_tankIconSrv, g_tankIconTex9, "TANK.png", "Tank icon");
}

static void HP_LoadHistoryIconTextureIfNeeded()
{
    HP_LoadNamedIconTextureIfNeeded(g_historyIconTexture, g_historyIconSrv, g_historyIconTex9, "HISTORY.png", "History icon");
}

static void HP_LoadSettingsIconTextureIfNeeded()
{
    HP_LoadNamedIconTextureIfNeeded(g_settingsIconTexture, g_settingsIconSrv, g_settingsIconTex9, "SETTINGS.png", "Settings icon");
}

static void HP_LoadGhostIconTextureIfNeeded()
{
    // Ghost.png is optional. The mini overlay already has a drawn fallback
    // ghost icon, so do not try to load a PNG here. This prevents an
    // unnecessary red chat warning when /healparse overlay on is used and
    // Ghost.png is not present at the exact expected path/casing.
    g_ghostIconTexture.attempted = true;
}

static void HP_LoadRefreshIconTextureIfNeeded()
{
    // Optional PNG for the mini DPS cycle/refresh button. Put this next to the
    // other HealTracker images as Cycle.png. If it is missing, the button
    // falls back to a text refresh symbol so the plugin still works.
    HP_LoadNamedIconTextureIfNeeded(g_refreshIconTexture, g_refreshIconSrv, g_refreshIconTex9, "Cycle.png", "Cycle icon");
}

static void HP_LoadCalIconTextureIfNeeded()
{
    // Optional calendar PNG for date filters. Put Cal.png in MQ2HealParse\\Images.
    // If missing, the date button falls back to plain text and still works.
    HP_LoadNamedIconTextureIfNeeded(g_calIconTexture, g_calIconSrv, g_calIconTex9, "Cal.png", "Calendar icon");
}

static void HP_LoadWizIconTextureIfNeeded()
{
    HP_LoadNamedIconTextureIfNeeded(g_wizIconTexture, g_wizIconSrv, g_wizIconTex9, "Wiz.png", "Wizard class icon");
}

static void HP_LoadEncIconTextureIfNeeded()
{
    HP_LoadNamedIconTextureIfNeeded(g_encIconTexture, g_encIconSrv, g_encIconTex9, "Enc.png", "Enchanter class icon");
}

static void HP_LoadClerIconTextureIfNeeded()
{
    HP_LoadNamedIconTextureIfNeeded(g_clerIconTexture, g_clerIconSrv, g_clerIconTex9, "Cler.png", "Cleric class icon");
}

static void HP_LoadNecIconTextureIfNeeded()
{
    HP_LoadNamedIconTextureIfNeeded(g_necIconTexture, g_necIconSrv, g_necIconTex9, "Nec.png", "Necromancer class icon");
}

static void HP_LoadMageIconTextureIfNeeded()
{
    HP_LoadNamedIconTextureIfNeeded(g_mageIconTexture, g_mageIconSrv, g_mageIconTex9, "Mage.png", "Mage class icon");
}

static void HP_LoadPalIconTextureIfNeeded()
{
    HP_LoadNamedIconTextureIfNeeded(g_palIconTexture, g_palIconSrv, g_palIconTex9, "Pal.png", "Paladin class icon");
}

static void HP_LoadBstIconTextureIfNeeded()
{
    HP_LoadNamedIconTextureIfNeeded(g_bstIconTexture, g_bstIconSrv, g_bstIconTex9, "BST.png", "Beastlord class icon");
}

static void HP_LoadRngIconTextureIfNeeded()
{
    HP_LoadNamedIconTextureIfNeeded(g_rngIconTexture, g_rngIconSrv, g_rngIconTex9, "RNG.png", "Ranger class icon");
}

static void HP_LoadBrdIconTextureIfNeeded()
{
    HP_LoadNamedIconTextureIfNeeded(g_brdIconTexture, g_brdIconSrv, g_brdIconTex9, "BRD.png", "Bard class icon");
}

static void HP_LoadBerIconTextureIfNeeded()
{
    HP_LoadNamedIconTextureIfNeeded(g_berIconTexture, g_berIconSrv, g_berIconTex9, "BER.png", "Berserker class icon");
}

static void HP_LoadDruIconTextureIfNeeded()
{
    HP_LoadNamedIconTextureIfNeeded(g_druIconTexture, g_druIconSrv, g_druIconTex9, "DRU.png", "Druid class icon");
}

static void HP_LoadMnkIconTextureIfNeeded()
{
    HP_LoadNamedIconTextureIfNeeded(g_mnkIconTexture, g_mnkIconSrv, g_mnkIconTex9, "MNK.png", "Monk class icon");
}

static void HP_LoadRogIconTextureIfNeeded()
{
    HP_LoadNamedIconTextureIfNeeded(g_rogIconTexture, g_rogIconSrv, g_rogIconTex9, "ROG.png", "Rogue class icon");
}

static void HP_LoadSkIconTextureIfNeeded()
{
    HP_LoadNamedIconTextureIfNeeded(g_skIconTexture, g_skIconSrv, g_skIconTex9, "SK.png", "Shadowknight class icon");
}

static void HP_LoadShmIconTextureIfNeeded()
{
    HP_LoadNamedIconTextureIfNeeded(g_shmIconTexture, g_shmIconSrv, g_shmIconTex9, "SHM.png", "Shaman class icon");
}

static void HP_LoadWarIconTextureIfNeeded()
{
    HP_LoadNamedIconTextureIfNeeded(g_warIconTexture, g_warIconSrv, g_warIconTex9, "WAR.png", "Warrior class icon");
}

static HP_IconTexture* HP_GetClassIconTexture(const std::string& cls)
{
    if (cls == "WIZ") { HP_LoadWizIconTextureIfNeeded(); return &g_wizIconTexture; }
    if (cls == "ENC") { HP_LoadEncIconTextureIfNeeded(); return &g_encIconTexture; }
    if (cls == "CLR") { HP_LoadClerIconTextureIfNeeded(); return &g_clerIconTexture; }
    if (cls == "NEC") { HP_LoadNecIconTextureIfNeeded(); return &g_necIconTexture; }
    if (cls == "MAG") { HP_LoadMageIconTextureIfNeeded(); return &g_mageIconTexture; }
    if (cls == "PAL") { HP_LoadPalIconTextureIfNeeded(); return &g_palIconTexture; }
    if (cls == "BST") { HP_LoadBstIconTextureIfNeeded(); return &g_bstIconTexture; }
    if (cls == "RNG") { HP_LoadRngIconTextureIfNeeded(); return &g_rngIconTexture; }
    if (cls == "BRD") { HP_LoadBrdIconTextureIfNeeded(); return &g_brdIconTexture; }
    if (cls == "BER") { HP_LoadBerIconTextureIfNeeded(); return &g_berIconTexture; }
    if (cls == "DRU") { HP_LoadDruIconTextureIfNeeded(); return &g_druIconTexture; }
    if (cls == "MNK") { HP_LoadMnkIconTextureIfNeeded(); return &g_mnkIconTexture; }
    if (cls == "ROG") { HP_LoadRogIconTextureIfNeeded(); return &g_rogIconTexture; }
    if (cls == "SHD" || cls == "SK") { HP_LoadSkIconTextureIfNeeded(); return &g_skIconTexture; }
    if (cls == "SHM") { HP_LoadShmIconTextureIfNeeded(); return &g_shmIconTexture; }
    if (cls == "WAR") { HP_LoadWarIconTextureIfNeeded(); return &g_warIconTexture; }
    return nullptr;
}

static void HP_ReleaseDemonIconTexture()
{
#ifdef _WIN32
    if (g_demonIconSrv) {
        g_demonIconSrv->Release();
        g_demonIconSrv = nullptr;
    }
    if (g_demonIconTex9) {
        g_demonIconTex9->Release();
        g_demonIconTex9 = nullptr;
    }
    if (g_swordsIconSrv) {
        g_swordsIconSrv->Release();
        g_swordsIconSrv = nullptr;
    }
    if (g_swordsIconTex9) {
        g_swordsIconTex9->Release();
        g_swordsIconTex9 = nullptr;
    }
    if (g_healsIconSrv) { g_healsIconSrv->Release(); g_healsIconSrv = nullptr; }
    if (g_healsIconTex9) { g_healsIconTex9->Release(); g_healsIconTex9 = nullptr; }
    if (g_dpsIconSrv) { g_dpsIconSrv->Release(); g_dpsIconSrv = nullptr; }
    if (g_dpsIconTex9) { g_dpsIconTex9->Release(); g_dpsIconTex9 = nullptr; }
    if (g_deathsIconSrv) { g_deathsIconSrv->Release(); g_deathsIconSrv = nullptr; }
    if (g_deathsIconTex9) { g_deathsIconTex9->Release(); g_deathsIconTex9 = nullptr; }
    if (g_playersIconSrv) { g_playersIconSrv->Release(); g_playersIconSrv = nullptr; }
    if (g_playersIconTex9) { g_playersIconTex9->Release(); g_playersIconTex9 = nullptr; }
    if (g_durationIconSrv) { g_durationIconSrv->Release(); g_durationIconSrv = nullptr; }
    if (g_durationIconTex9) { g_durationIconTex9->Release(); g_durationIconTex9 = nullptr; }
    if (g_spellsIconSrv) { g_spellsIconSrv->Release(); g_spellsIconSrv = nullptr; }
    if (g_spellsIconTex9) { g_spellsIconTex9->Release(); g_spellsIconTex9 = nullptr; }
    if (g_tankIconSrv) { g_tankIconSrv->Release(); g_tankIconSrv = nullptr; }
    if (g_tankIconTex9) { g_tankIconTex9->Release(); g_tankIconTex9 = nullptr; }
    if (g_historyIconSrv) { g_historyIconSrv->Release(); g_historyIconSrv = nullptr; }
    if (g_historyIconTex9) { g_historyIconTex9->Release(); g_historyIconTex9 = nullptr; }
    if (g_settingsIconSrv) { g_settingsIconSrv->Release(); g_settingsIconSrv = nullptr; }
    if (g_settingsIconTex9) { g_settingsIconTex9->Release(); g_settingsIconTex9 = nullptr; }
    if (g_ghostIconSrv) { g_ghostIconSrv->Release(); g_ghostIconSrv = nullptr; }
    if (g_ghostIconTex9) { g_ghostIconTex9->Release(); g_ghostIconTex9 = nullptr; }
    if (g_refreshIconSrv) { g_refreshIconSrv->Release(); g_refreshIconSrv = nullptr; }
    if (g_refreshIconTex9) { g_refreshIconTex9->Release(); g_refreshIconTex9 = nullptr; }
    if (g_calIconSrv) { g_calIconSrv->Release(); g_calIconSrv = nullptr; }
    if (g_calIconTex9) { g_calIconTex9->Release(); g_calIconTex9 = nullptr; }
    if (g_wizIconSrv) { g_wizIconSrv->Release(); g_wizIconSrv = nullptr; }
    if (g_wizIconTex9) { g_wizIconTex9->Release(); g_wizIconTex9 = nullptr; }
    if (g_encIconSrv) { g_encIconSrv->Release(); g_encIconSrv = nullptr; }
    if (g_encIconTex9) { g_encIconTex9->Release(); g_encIconTex9 = nullptr; }
    if (g_clerIconSrv) { g_clerIconSrv->Release(); g_clerIconSrv = nullptr; }
    if (g_clerIconTex9) { g_clerIconTex9->Release(); g_clerIconTex9 = nullptr; }
    if (g_necIconSrv) { g_necIconSrv->Release(); g_necIconSrv = nullptr; }
    if (g_necIconTex9) { g_necIconTex9->Release(); g_necIconTex9 = nullptr; }
    if (g_mageIconSrv) { g_mageIconSrv->Release(); g_mageIconSrv = nullptr; }
    if (g_mageIconTex9) { g_mageIconTex9->Release(); g_mageIconTex9 = nullptr; }
    if (g_palIconSrv) { g_palIconSrv->Release(); g_palIconSrv = nullptr; }
    if (g_palIconTex9) { g_palIconTex9->Release(); g_palIconTex9 = nullptr; }
    if (g_bstIconSrv) { g_bstIconSrv->Release(); g_bstIconSrv = nullptr; }
    if (g_bstIconTex9) { g_bstIconTex9->Release(); g_bstIconTex9 = nullptr; }
    if (g_rngIconSrv) { g_rngIconSrv->Release(); g_rngIconSrv = nullptr; }
    if (g_rngIconTex9) { g_rngIconTex9->Release(); g_rngIconTex9 = nullptr; }
    if (g_brdIconSrv) { g_brdIconSrv->Release(); g_brdIconSrv = nullptr; }
    if (g_brdIconTex9) { g_brdIconTex9->Release(); g_brdIconTex9 = nullptr; }
    if (g_berIconSrv) { g_berIconSrv->Release(); g_berIconSrv = nullptr; }
    if (g_berIconTex9) { g_berIconTex9->Release(); g_berIconTex9 = nullptr; }
    if (g_druIconSrv) { g_druIconSrv->Release(); g_druIconSrv = nullptr; }
    if (g_druIconTex9) { g_druIconTex9->Release(); g_druIconTex9 = nullptr; }
    if (g_mnkIconSrv) { g_mnkIconSrv->Release(); g_mnkIconSrv = nullptr; }
    if (g_mnkIconTex9) { g_mnkIconTex9->Release(); g_mnkIconTex9 = nullptr; }
    if (g_rogIconSrv) { g_rogIconSrv->Release(); g_rogIconSrv = nullptr; }
    if (g_rogIconTex9) { g_rogIconTex9->Release(); g_rogIconTex9 = nullptr; }
    if (g_skIconSrv) { g_skIconSrv->Release(); g_skIconSrv = nullptr; }
    if (g_skIconTex9) { g_skIconTex9->Release(); g_skIconTex9 = nullptr; }
    if (g_shmIconSrv) { g_shmIconSrv->Release(); g_shmIconSrv = nullptr; }
    if (g_shmIconTex9) { g_shmIconTex9->Release(); g_shmIconTex9 = nullptr; }
    if (g_warIconSrv) { g_warIconSrv->Release(); g_warIconSrv = nullptr; }
    if (g_warIconTex9) { g_warIconTex9->Release(); g_warIconTex9 = nullptr; }
    for (auto& kv : g_mobIconTextures) {
        if (kv.second.srv) { kv.second.srv->Release(); kv.second.srv = nullptr; }
        if (kv.second.tex9) { kv.second.tex9->Release(); kv.second.tex9 = nullptr; }
    }
#endif
    g_mobIconTextures.clear();
    g_demonIconTexture = HP_IconTexture{};
    g_swordsIconTexture = HP_IconTexture{};
    g_healsIconTexture = HP_IconTexture{};
    g_dpsIconTexture = HP_IconTexture{};
    g_deathsIconTexture = HP_IconTexture{};
    g_playersIconTexture = HP_IconTexture{};
    g_durationIconTexture = HP_IconTexture{};
    g_spellsIconTexture = HP_IconTexture{};
    g_tankIconTexture = HP_IconTexture{};
    g_historyIconTexture = HP_IconTexture{};
    g_settingsIconTexture = HP_IconTexture{};
    g_ghostIconTexture = HP_IconTexture{};
    g_refreshIconTexture = HP_IconTexture{};
    g_calIconTexture = HP_IconTexture{};
    g_wizIconTexture = HP_IconTexture{};
    g_encIconTexture = HP_IconTexture{};
    g_clerIconTexture = HP_IconTexture{};
    g_necIconTexture = HP_IconTexture{};
    g_mageIconTexture = HP_IconTexture{};
    g_palIconTexture = HP_IconTexture{};
    g_bstIconTexture = HP_IconTexture{};
    g_rngIconTexture = HP_IconTexture{};
    g_brdIconTexture = HP_IconTexture{};
    g_berIconTexture = HP_IconTexture{};
    g_druIconTexture = HP_IconTexture{};
    g_mnkIconTexture = HP_IconTexture{};
    g_rogIconTexture = HP_IconTexture{};
    g_skIconTexture = HP_IconTexture{};
    g_shmIconTexture = HP_IconTexture{};
    g_warIconTexture = HP_IconTexture{};
}

static void HP_DrawFallbackDemonIcon(ImDrawList* dl, ImVec2 p, float size)
{
    if (!dl) return;
    ImVec2 c(p.x + size * 0.5f, p.y + size * 0.5f);
    float r = size * 0.42f;
    dl->AddCircleFilled(c, r, IM_COL32(150, 25, 25, 255), 18);
    dl->AddCircle(c, r, IM_COL32(255, 90, 70, 255), 18, 2.0f);
    dl->AddTriangleFilled(ImVec2(c.x - r * 0.85f, c.y - r * 0.15f), ImVec2(c.x - r * 1.35f, c.y - r * 0.75f), ImVec2(c.x - r * 0.35f, c.y - r * 0.55f), IM_COL32(230, 215, 180, 255));
    dl->AddTriangleFilled(ImVec2(c.x + r * 0.85f, c.y - r * 0.15f), ImVec2(c.x + r * 1.35f, c.y - r * 0.75f), ImVec2(c.x + r * 0.35f, c.y - r * 0.55f), IM_COL32(230, 215, 180, 255));
    dl->AddCircleFilled(ImVec2(c.x - r * 0.35f, c.y - r * 0.08f), r * 0.13f, IM_COL32(80, 230, 255, 255), 10);
    dl->AddCircleFilled(ImVec2(c.x + r * 0.35f, c.y - r * 0.08f), r * 0.13f, IM_COL32(80, 230, 255, 255), 10);
}


static void HP_DrawImageIcon(ImDrawList* dl, HP_IconTexture& tex, ImVec2 p, float size)
{
    if (dl && tex.id)
        dl->AddImage(tex.id, p, ImVec2(p.x + size, p.y + size));
}

static void HP_DrawPanelTitleIconText(HP_IconTexture& tex, const char* title, ImVec4 color, float iconSize = 18.0f)
{
    if (tex.id) {
        ImGui::Image(tex.id, ImVec2(iconSize, iconSize));
        ImGui::SameLine(0.0f, 6.0f);
        ImGui::SetCursorPosY(ImGui::GetCursorPosY() + 1.0f);
    }
    ImGui::TextColored(color, "%s", title);
}


static const char* HP_MobRaceNameFromId(int race);
static std::string HP_MobBodyTypeIconKey(int bodyType);
static std::string HP_MobRaceGroupIconKey(int race, const std::string& raceName);
static std::string HP_NormalizeIconKey(std::string key);
static std::string HP_MobKeywordIconKey(const std::string& mobName);
static bool HP_TextLooksLikeDragon(const std::string& s);
static std::string HP_MobIconKeyFromAnyText(const std::string& s);
static bool HP_MobIconIsDragon(int race, int bodyType, const std::string& iconKey, const std::string& mobName);
static void HP_DrawDemonIconInList(ImDrawList* dl, ImVec2 p, float size);

static std::vector<std::string> HP_GetMobIconCandidateFileNames(int race, int bodyType, const std::string& iconKey, const std::string& mobName)
{
    std::vector<std::string> out;
    auto addUnique = [&](const std::string& v) {
        if (v.empty()) return;
        for (const auto& e : out) if (LowerCopy(e) == LowerCopy(v)) return;
        out.push_back(v);
    };
    auto addKey = [&](const std::string& raw) {
        std::string k = HP_NormalizeIconKey(raw);
        if (k.empty()) return;
        addUnique(std::string("Mobs\\") + k + ".png");
        addUnique(k + ".png");
    };

    // Hard dragon override. If MQ gives us Dragon in any reliable field, try
    // Dragon.png first. This avoids Body/Race ID mismatches on custom servers.
    if (HP_MobIconIsDragon(race, bodyType, iconKey, mobName))
        addKey("Dragon");

    // Hard Sarnak override. Project Lazarus Di`zok/Sarnak mobs can report as
    // Humanoid/Human through some C++ spawn fields while ${Target.Race} shows
    // Sarnak. Try Sarnak.png first whenever any reliable field identifies it.
    {
        const char* rn = HP_MobRaceNameFromId(race);
        std::string sarnakProbe = LowerCopy(HP_NormalizeIconKey(std::string(rn ? rn : "") + " " + iconKey + " " + mobName));
        if (race == 131 || sarnakProbe.find("sarnak") != std::string::npos || sarnakProbe.find("dizok") != std::string::npos)
            addKey("Sarnak");
    }

    // Hard Griffin override. Some builds report Griffin correctly through
    // ${Target.Race}, while cached numeric/body fields may still fall through
    // to Demon. Try Griffin.png first whenever any reliable field identifies it.
    {
        const char* rn = HP_MobRaceNameFromId(race);
        std::string griffinProbe = LowerCopy(HP_NormalizeIconKey(std::string(rn ? rn : "") + " " + iconKey + " " + mobName));
        if (race == 48 || griffinProbe.find("griffin") != std::string::npos || griffinProbe.find("griffon") != std::string::npos)
            addKey("Griffin");
    }

    // Race must win before BodyType. Some EQ/MQ targets report examples like:
    //   Race: Dragon   Body: Puff Dragon
    // If BodyType is tried first, a generic/body-specific image can hide the
    // correct race portrait. So the order is now:
    //   Race_<id>.png -> RaceName.png -> RaceGroup.png -> saved iconKey ->
    //   Body_<id>.png -> BodyGroup.png -> mob-name keyword -> Demon fallback.
    const char* raceName = HP_MobRaceNameFromId(race);
    if (race > 0) {
        addUnique(std::string("Mobs\\Race_") + std::to_string(race) + ".png");
        addUnique(std::string("Race_") + std::to_string(race) + ".png");
    }

    // Friendly race and race-family icons next. This makes a mob with
    // Race:Dragon use Dragon.png even when Body says Puff Dragon.
    addKey(raceName ? raceName : "");
    addKey(HP_MobRaceGroupIconKey(race, raceName ? raceName : ""));

    // If a previous cache/history row only saved the icon key text, still let
    // that text win before body fallback. Example: iconKey = Dragon.
    addKey(iconKey);

    // Body is only a fallback now. BodyType is still useful for generic
    // Undead/Animal/Construct/etc. icons when race is unknown or unmapped.
    if (bodyType > 0) {
        addUnique(std::string("Mobs\\Body_") + std::to_string(bodyType) + ".png");
        addUnique(std::string("Body_") + std::to_string(bodyType) + ".png");
    }
    addKey(HP_MobBodyTypeIconKey(bodyType));
    addKey(HP_MobKeywordIconKey(mobName));
    return out;
}

static HP_IconTexture* HP_GetMobIconTextureForFight(int race, int bodyType, const std::string& iconKey, const std::string& mobName)
{
    std::vector<std::string> files = HP_GetMobIconCandidateFileNames(race, bodyType, iconKey, mobName);

    const int frame = ImGui::GetFrameCount();
    if (g_mobIconTextureLoadFrame != frame) {
        g_mobIconTextureLoadFrame = frame;
        g_mobIconTextureLoadsThisFrame = 0;
    }

    for (const std::string& file : files) {
        std::string mapKey = LowerCopy(file);
        HP_MobIconTextureEntry& ent = g_mobIconTextures[mapKey];

        // Fast path: already loaded. No file checks, no disk I/O.
        if (ent.tex.id) return &ent.tex;

        // Slow path: first-time PNG discovery/load. Limit to one mob-icon
        // texture attempt per frame so killing a mob cannot trigger a burst of
        // Body/Race/category/keyword file probes all in the same frame.
        if (!ent.tex.attempted) {
            if (g_mobIconTextureLoadsThisFrame >= kMaxMobIconTextureLoadsPerFrame)
                return nullptr;
            ++g_mobIconTextureLoadsThisFrame;
#ifdef _WIN32
            HP_LoadNamedIconTextureIfNeeded(ent.tex, ent.srv, ent.tex9, file.c_str(), "mob icon");
#else
            ent.tex.attempted = true;
#endif
            if (ent.tex.id) return &ent.tex;
        }
    }
    return nullptr;
}

static void HP_DrawMobIconInList(ImDrawList* dl, ImVec2 p, float size, int race, int bodyType, const std::string& iconKey, const std::string& mobName)
{
    if (HP_IconTexture* tex = HP_GetMobIconTextureForFight(race, bodyType, iconKey, mobName)) {
        if (dl && tex->id) {
            dl->AddImage(tex->id, p, ImVec2(p.x + size, p.y + size));
            return;
        }
    }
    HP_DrawDemonIconInList(dl, p, size);
}

static void HP_DrawDemonIconInList(ImDrawList* dl, ImVec2 p, float size)
{
    HP_LoadDemonIconTextureIfNeeded();
    if (dl && g_demonIconTexture.id) {
        dl->AddImage(g_demonIconTexture.id, p, ImVec2(p.x + size, p.y + size));
    } else {
        HP_DrawFallbackDemonIcon(dl, p, size);
    }
}

static void HP_DrawSwordsIcon(ImDrawList* dl, ImVec2 p, float size)
{
    HP_LoadSwordsIconTextureIfNeeded();
    if (dl && g_swordsIconTexture.id) {
        // Swords image is wide; draw it square-ish with the full texture scaled down.
        dl->AddImage(g_swordsIconTexture.id, p, ImVec2(p.x + size, p.y + size));
    } else if (dl) {
        ImVec2 c(p.x + size * 0.5f, p.y + size * 0.5f);
        dl->AddText(ImVec2(p.x + 2.0f, p.y + 1.0f), IM_COL32(190, 160, 255, 255), "X");
        dl->AddLine(ImVec2(c.x - size * .28f, c.y - size * .30f), ImVec2(c.x + size * .28f, c.y + size * .30f), IM_COL32(200, 190, 255, 255), 3.0f);
        dl->AddLine(ImVec2(c.x + size * .28f, c.y - size * .30f), ImVec2(c.x - size * .28f, c.y + size * .30f), IM_COL32(200, 190, 255, 255), 3.0f);
    }
}

static void HP_DrawHealtrackerLogo(ImDrawList* dl, ImVec2 p, float maxW, float maxH)
{
    HP_LoadHealtrackerLogoTextureIfNeeded();
    if (!dl || !g_healtrackerLogoTexture.id) return;

    float texW = (float)std::max(1, g_healtrackerLogoTexture.width);
    float texH = (float)std::max(1, g_healtrackerLogoTexture.height);
    float scale = std::min(maxW / texW, maxH / texH);
    if (scale <= 0.0f) scale = 1.0f;

    float drawW = texW * scale;
    float drawH = texH * scale;
    dl->AddImage(g_healtrackerLogoTexture.id, p, ImVec2(p.x + drawW, p.y + drawH));
}



static std::string HP_EscapeField(const std::string& v)
{
    std::string out;
    out.reserve(v.size() + 8);
    for (char c : v) {
        if (c == '\\') out += "\\\\";
        else if (c == '|') out += "\\p";
        else if (c == '\n') out += "\\n";
        else if (c == '\r') out += "\\r";
        else out.push_back(c);
    }
    return out;
}

static std::vector<std::string> HP_SplitEscaped(const std::string& line)
{
    std::vector<std::string> parts;
    std::string cur;
    bool esc = false;
    for (char c : line) {
        if (esc) {
            if (c == 'p') cur.push_back('|');
            else if (c == 'n') cur.push_back('\n');
            else if (c == 'r') cur.push_back('\r');
            else cur.push_back(c);
            esc = false;
        } else if (c == '\\') {
            esc = true;
        } else if (c == '|') {
            parts.push_back(cur);
            cur.clear();
        } else {
            cur.push_back(c);
        }
    }
    parts.push_back(cur);
    return parts;
}

static uint64_t HP_ParseU64(const std::string& s)
{
    if (s.empty()) return 0;
    return static_cast<uint64_t>(std::strtoull(s.c_str(), nullptr, 10));
}

static int64_t HP_ParseI64(const std::string& s)
{
    if (s.empty()) return 0;
    return static_cast<int64_t>(std::strtoll(s.c_str(), nullptr, 10));
}

static bool HP_ContainsNoCase(const std::string& hay, const char* needle);

static int64_t HP_WallNow()
{
    return static_cast<int64_t>(std::time(nullptr));
}

static std::string HP_FormatDateOnly(int64_t wall)
{
    if (wall <= 0) return "Unknown";
    std::time_t t = static_cast<std::time_t>(wall);
    std::tm tmv{};
#ifdef _WIN32
    localtime_s(&tmv, &t);
#else
    localtime_r(&t, &tmv);
#endif
    char buf[32] = {0};
    std::strftime(buf, sizeof(buf), "%m/%d/%Y", &tmv);
    return buf;
}

static std::string HP_FormatTimeOnly(int64_t wall)
{
    if (wall <= 0) return "--:--";
    std::time_t t = static_cast<std::time_t>(wall);
    std::tm tmv{};
#ifdef _WIN32
    localtime_s(&tmv, &t);
#else
    localtime_r(&t, &tmv);
#endif
    char buf[32] = {0};
    std::strftime(buf, sizeof(buf), "%I:%M %p", &tmv);
    return buf;
}

static std::string HP_FormatTimeWithSeconds(int64_t wall)
{
    if (wall <= 0) return "--:--:--";
    std::time_t t = static_cast<std::time_t>(wall);
    std::tm tmv{};
#ifdef _WIN32
    localtime_s(&tmv, &t);
#else
    localtime_r(&t, &tmv);
#endif
    char buf[32] = {0};
    std::strftime(buf, sizeof(buf), "%I:%M:%S %p", &tmv);
    return buf;
}

static const char* HP_ClassNameFromId(int cls)
{
    switch (cls) {
    case 1: return "WAR"; case 2: return "CLR"; case 3: return "PAL"; case 4: return "RNG";
    case 5: return "SHD"; case 6: return "DRU"; case 7: return "MNK"; case 8: return "BRD";
    case 9: return "ROG"; case 10: return "SHM"; case 11: return "NEC"; case 12: return "WIZ";
    case 13: return "MAG"; case 14: return "ENC"; case 15: return "BST"; case 16: return "BER";
    default: return "-";
    }
}

static void HP_SavePlayerClassCacheUnlocked()
{
    std::ofstream out(kPlayerClassCacheFileName, std::ios::out | std::ios::trunc);
    if (!out.good()) return;
    out << "# HealParse Player Classes v1\n";
    for (const auto& kv : g_playerClassCache) {
        if (!kv.first.empty() && !kv.second.empty() && kv.second != "-")
            out << kv.first << '\t' << kv.second << "\n";
    }
}

static void HP_LoadPlayerClassCache()
{
    std::ifstream in(kPlayerClassCacheFileName);
    if (!in.good()) return;

    std::lock_guard<std::mutex> lk(g_playerClassCacheMutex);
    std::string line;
    while (std::getline(in, line)) {
        if (line.empty() || line[0] == '#') continue;
        size_t tab = line.find('\t');
        if (tab == std::string::npos) continue;
        std::string player = line.substr(0, tab);
        std::string cls = line.substr(tab + 1);
        if (!player.empty() && !cls.empty() && cls != "-")
            g_playerClassCache[player] = cls;
    }
}

static void HP_RememberPlayerClass(const std::string& name, const std::string& cls)
{
    if (name.empty() || cls.empty() || cls == "-") return;

    std::lock_guard<std::mutex> lk(g_playerClassCacheMutex);
    auto it = g_playerClassCache.find(name);
    if (it != g_playerClassCache.end() && it->second == cls) return;
    g_playerClassCache[name] = cls;
    HP_SavePlayerClassCacheUnlocked();
}

static std::string HP_GetCachedPlayerClassName(const std::string& name)
{
    if (name.empty()) return "-";
    std::lock_guard<std::mutex> lk(g_playerClassCacheMutex);

    auto it = g_playerClassCache.find(name);
    if (it != g_playerClassCache.end() && !it->second.empty())
        return it->second;

    std::string lower = LowerCopy(name);
    for (const auto& kv : g_playerClassCache) {
        if (LowerCopy(kv.first) == lower && !kv.second.empty())
            return kv.second;
    }
    return "-";
}

static std::string HP_GetPlayerClassName(const std::string& name)
{
    if (name.empty()) return "-";

    if (pSpawnManager) {
        for (PlayerClient* cur = pSpawnManager->FirstSpawn; cur; cur = cur->GetNext()) {
            const char* dn = cur->DisplayedName;
            const char* nm = cur->Name;
            bool nameMatch = (dn && dn[0] && name == dn) || (nm && nm[0] && name == nm);
            if (!nameMatch) continue;
            if (cur->Type == SPAWN_PLAYER) {
                std::string cls = HP_ClassNameFromId((int)cur->GetClass());
                HP_RememberPlayerClass(name, cls);
                if (dn && dn[0]) HP_RememberPlayerClass(dn, cls);
                if (nm && nm[0]) HP_RememberPlayerClass(nm, cls);
                return cls;
            }
        }
    }

    // Player is not currently in-zone or spawn manager is unavailable.
    // Fall back to the persistent class cache so old fights keep their class
    // abbreviation and class PNG emblem.
    return HP_GetCachedPlayerClassName(name);
}


// ----------------------------------------------------------------------------
// Mob race/body-type cache for fight icons.
// The combat log only gives a mob display name, so when a fight starts while the
// NPC is still alive/in-zone we grab its spawn race/body type from MQ and save
// that data with the completed fight.  Icon lookup prefers:
//   Images\Mobs\Body_<body>.png
//   Images\Mobs\Race_<race>.png
//   Images\Mobs\<RaceName>.png
//   Images\Mobs\<keyword from mob name>.png
// then falls back to Demon.png.
// ----------------------------------------------------------------------------
struct HP_MobSpawnInfo {
    int race = 0;
    int bodyType = 0;
    std::string iconKey;      // exact/best icon key, usually race name
    std::string bodyKey;      // broad EQ body family: Animal, Undead, Humanoid, etc.
    std::string raceGroupKey; // broad race family: Goblin, Orc, Dragon, Undead, etc.
    int64_t lastSeenWall = 0;
};

// Persistent mob-name -> race/body cache. This lets old fight names keep their
// correct icon even after the mob despawns or after MQ2HealParse is rebuilt.
// It is also useful when a later combat line starts a fight but the target is
// no longer findable in the spawn list.
static std::unordered_map<std::string, HP_MobSpawnInfo> g_mobSpawnInfoCache;
static std::mutex g_mobSpawnInfoCacheMutex;
static std::atomic<bool> g_mobSpawnInfoCacheDirty{ false };

static const char* HP_MobRaceNameFromId(int race)
{
    switch (race) {
    case 1: return "Human"; case 2: return "Barbarian"; case 3: return "Erudite";
    case 4: return "WoodElf"; case 5: return "HighElf"; case 6: return "DarkElf";
    case 7: return "HalfElf"; case 8: return "Dwarf"; case 9: return "Troll";
    case 10: return "Ogre"; case 11: return "Halfling"; case 12: return "Gnome";
    case 13: return "Aviak"; case 14: return "Werewolf"; case 15: return "Brownie";
    case 16: return "Centaur"; case 17: return "Golem"; case 18: return "Giant";
    case 21: return "EvilEye"; case 22: return "Beetle"; case 23: return "Kerran";
    case 24: return "Fish"; case 25: return "Fairy"; case 26: return "Froglok";
    case 27: return "FroglokGhoul"; case 28: return "Fungusman"; case 29: return "Gargoyle";
    case 30: return "Gasbag"; case 31: return "GelatinousCube"; case 32: return "Ghost";
    case 33: return "Ghoul"; case 34: return "Bat"; case 35: return "Eel";
    case 36: return "Rat"; case 37: return "Snake"; case 38: return "Spider";
    case 39: return "Gnoll"; case 40: return "Goblin"; case 41: return "Gorilla";
    case 42: return "Wolf"; case 43: return "Bear"; case 46: return "DemiLich";
    case 47: return "Imp"; case 48: return "Griffin"; case 49: return "Kobold";
    case 50: return "Dragon"; case 53: return "Lion"; case 54: return "LizardMan";
    case 55: return "Mimic"; case 56: return "Minotaur"; case 57: return "Orc";
    case 58: return "Beggar"; case 60: return "Pixie"; case 62: return "Skeleton";
    case 63: return "Shark"; case 64: return "Tunare"; case 65: return "Tiger";
    case 66: return "Treant"; case 67: return "Vampire"; case 68: return "Statue";
    case 69: return "HighpassCitizen"; case 70: return "Tentacle"; case 71: return "WillOWisp";
    case 72: return "Zombie"; case 73: return "QeynosCitizen"; case 74: return "Ship";
    case 75: return "Launch"; case 76: return "Piranha"; case 77: return "Elemental";
    case 78: return "Puma"; case 79: return "DarkElfCitizen"; case 80: return "EruditeCitizen";
    case 81: return "Bixie"; case 82: return "ReanimatedHand"; case 83: return "RivervaleCitizen";
    case 84: return "Scarecrow"; case 85: return "Skunk"; case 86: return "SnakeElemental";
    case 87: return "Spectre"; case 88: return "Sphinx"; case 89: return "Armadillo";
    case 90: return "ClockworkGnome"; case 91: return "Drake"; case 92: return "HalasCitizen";
    case 93: return "Alligator"; case 94: return "GrobbCitizen"; case 95: return "OggokCitizen";
    case 96: return "KaladimCitizen"; case 97: return "CazicThule"; case 98: return "Cockatrice";
    case 99: return "DaisyMan"; case 100: return "Vampire2"; case 101: return "Amygdalan";
    case 102: return "Dervish"; case 103: return "Efreeti"; case 104: return "Tadpole";
    case 105: return "Kedge"; case 106: return "Leech"; case 107: return "Swordfish";
    case 108: return "Guard"; case 109: return "Mammoth"; case 110: return "EyeOfZomm";
    case 111: return "Wasp"; case 112: return "Mermaid"; case 113: return "Harpie";
    case 114: return "Fayguard"; case 115: return "Drixie"; case 116: return "GhostShip";
    case 117: return "Clam"; case 118: return "Seahorse"; case 119: return "GhostGuard";
    case 120: return "GhostDwarf"; case 121: return "DynLeth"; case 122: return "Boat";
    case 123: return "HalasCitizen2"; case 124: return "EruditeGhost"; case 125: return "FireElemental";
    case 126: return "AirElemental"; case 127: return "WaterElemental"; case 128: return "EarthElemental";
    case 130: return "VahShir"; case 131: return "Sarnak"; case 330: return "Froglok"; case 522: return "Drakkin";
    default: return "";
    }
}


static std::string HP_MobBodyTypeIconKey(int bodyType)
{
    // Common EQ BodyType families. Values can vary on custom servers, so this
    // is intentionally only a broad fallback; exact Body_<id>.png is tried first.
    switch (bodyType) {
    case 1: return "Humanoid";
    case 2: return "Lycanthrope";
    case 3: return "Undead";
    case 4: return "Giant";
    case 5: return "Construct";
    case 6: return "Extraplanar";
    case 7: return "Magical";
    case 8: return "Undead";
    case 9: return "Summoned";
    case 10: return "Animal";
    case 11: return "Plant";
    case 12: return "Dragon";
    case 13: return "Summoned";
    case 14: return "Summoned";
    case 15: return "Monster";
    case 16: return "Insect";
    default: return std::string();
    }
}

static bool HP_RaceNameHasAny(const std::string& raceName, std::initializer_list<const char*> words)
{
    std::string r = LowerCopy(raceName);
    for (const char* w : words) {
        if (w && *w && r.find(LowerCopy(w)) != std::string::npos) return true;
    }
    return false;
}

static bool HP_TextLooksLikeDragon(const std::string& s)
{
    std::string n = LowerCopy(HP_NormalizeIconKey(s));
    return n.find("dragon") != std::string::npos
        || n.find("drake") != std::string::npos
        || n.find("wyrm") != std::string::npos
        || n.find("wurm") != std::string::npos
        || n.find("wyvern") != std::string::npos;
}

static std::string HP_MobIconKeyFromAnyText(const std::string& s)
{
    std::string n = LowerCopy(HP_NormalizeIconKey(s));
    if (n.empty()) return std::string();

    struct Rule { const char* find; const char* key; };
    static const Rule rules[] = {
        {"sarnak", "Sarnak"}, {"dizok", "Sarnak"}, {"di_zok", "Sarnak"},
        {"griffin", "Griffin"}, {"griffon", "Griffin"},
        {"vahshir", "VahShir"}, {"vah", "VahShir"},
        {"iksar", "Iksar"}, {"drakkin", "Drakkin"},
        {"woodelf", "WoodElf"}, {"highelf", "HighElf"}, {"darkelf", "DarkElf"}, {"halfelf", "HalfElf"},
        {"barbarian", "Barbarian"}, {"erudite", "Erudite"}, {"halfling", "Halfling"},
        {"human", "Human"}, {"dwarf", "Dwarf"}, {"troll", "Troll"}, {"ogre", "Ogre"}, {"gnome", "Gnome"},
        {"goblin", "Goblin"}, {"orc", "Orc"}, {"gnoll", "Gnoll"}, {"kobold", "Kobold"}, {"froglok", "Froglok"},
        {"lizardman", "LizardMan"}, {"lizard", "LizardMan"}, {"aviak", "Aviak"}, {"centaur", "Centaur"},
        {"dragon", "Dragon"}, {"drake", "Dragon"}, {"wyrm", "Dragon"}, {"wurm", "Dragon"}, {"wyvern", "Dragon"},
        {"skeleton", "Undead"}, {"skeletal", "Undead"}, {"zombie", "Undead"}, {"ghoul", "Undead"},
        {"ghost", "Undead"}, {"spectre", "Undead"}, {"wraith", "Undead"}, {"vampire", "Undead"}, {"lich", "Undead"}, {"undead", "Undead"},
        {"wolf", "Animal"}, {"bear", "Animal"}, {"bat", "Animal"}, {"rat", "Animal"}, {"snake", "Animal"},
        {"spider", "Animal"}, {"gorilla", "Animal"}, {"lion", "Animal"}, {"tiger", "Animal"}, {"puma", "Animal"},
        {"cat", "Animal"}, {"mammoth", "Animal"}, {"alligator", "Animal"},
        {"beetle", "Insect"}, {"bixie", "Insect"}, {"wasp", "Insect"}, {"bee", "Insect"},
        {"fish", "Aquatic"}, {"shark", "Aquatic"}, {"eel", "Aquatic"}, {"piranha", "Aquatic"}, {"kedge", "Aquatic"},
        {"elemental", "Elemental"}, {"efreet", "Elemental"},
        {"golem", "Construct"}, {"construct", "Construct"}, {"clockwork", "Construct"}, {"statue", "Construct"},
        {"treant", "Plant"}, {"fungus", "Plant"}, {"mushroom", "Plant"}, {"plant", "Plant"},
        {"giant", "Giant"}, {"cyclops", "Giant"}, {"minotaur", "Giant"},
        {"imp", "Demon"}, {"demon", "Demon"}, {"gargoyle", "Demon"}
    };
    for (const Rule& r : rules) {
        if (n.find(r.find) != std::string::npos) return r.key;
    }
    return std::string();
}

static bool HP_MobIconIsDragon(int race, int bodyType, const std::string& iconKey, const std::string& mobName)
{
    const char* raceName = HP_MobRaceNameFromId(race);
    std::string bodyKey = HP_MobBodyTypeIconKey(bodyType);
    if (race == 50 || race == 91 || race == 165 || race == 184 || race == 192 || race == 198 || race == 208 || race == 209 || race == 304 || race == 330) return true;
    if (bodyType == 12) return true; // common MQ BodyType dragon family
    if (raceName && HP_TextLooksLikeDragon(raceName)) return true;
    if (HP_TextLooksLikeDragon(bodyKey)) return true;
    if (HP_TextLooksLikeDragon(iconKey)) return true;
    if (HP_TextLooksLikeDragon(mobName)) return true;
    return false;
}

static std::string HP_MobRaceGroupIconKey(int race, const std::string& raceName)
{
    // Group by known EQ families. This does not replace Race_<id>.png; it gives
    // you useful shared icons like Undead.png, Animal.png, Insect.png, Humanoid.png.
    if (HP_RaceNameHasAny(raceName, {"Skeleton", "Zombie", "Ghoul", "Ghost", "Spectre", "Vampire", "Lich", "DemiLich", "Reanimated", "Undead"})) return "Undead";
    if (HP_RaceNameHasAny(raceName, {"Wolf", "Bear", "Bat", "Rat", "Snake", "Spider", "Gorilla", "Lion", "Tiger", "Puma", "Mammoth", "Alligator", "Skunk", "Armadillo", "Cockatrice"})) return "Animal";
    if (HP_RaceNameHasAny(raceName, {"Fish", "Shark", "Eel", "Piranha", "Swordfish", "Leech", "Clam", "Seahorse", "Kedge", "Mermaid"})) return "Aquatic";
    if (HP_RaceNameHasAny(raceName, {"Beetle", "Bixie", "Wasp", "Drixie", "Spider"})) return "Insect";
    if (HP_RaceNameHasAny(raceName, {"Elemental", "Efreeti"})) return "Elemental";
    if (HP_RaceNameHasAny(raceName, {"Griffin", "Griffon"})) return "Griffin";
    if (HP_RaceNameHasAny(raceName, {"Dragon", "Drake", "Wurm", "Wyvern"})) return "Dragon";
    if (HP_RaceNameHasAny(raceName, {"Golem", "Construct", "Clockwork", "Statue", "Mimic"})) return "Construct";
    if (HP_RaceNameHasAny(raceName, {"Treant", "Fungus", "Plant", "Daisy"})) return "Plant";
    if (HP_RaceNameHasAny(raceName, {"VahShir"})) return "VahShir";
    if (HP_RaceNameHasAny(raceName, {"Iksar"})) return "Iksar";
    if (HP_RaceNameHasAny(raceName, {"Drakkin"})) return "Drakkin";
    if (HP_RaceNameHasAny(raceName, {"Sarnak", "DiZok", "Dizok"})) return "Sarnak";
    if (HP_RaceNameHasAny(raceName, {"Human", "Barbarian", "Erudite", "Elf", "Dwarf", "Halfling", "Gnome", "Citizen", "Guard", "Beggar"})) return "Humanoid";
    if (HP_RaceNameHasAny(raceName, {"Goblin"})) return "Goblin";
    if (HP_RaceNameHasAny(raceName, {"Orc"})) return "Orc";
    if (HP_RaceNameHasAny(raceName, {"Gnoll"})) return "Gnoll";
    if (HP_RaceNameHasAny(raceName, {"Kobold"})) return "Kobold";
    if (HP_RaceNameHasAny(raceName, {"Froglok"})) return "Froglok";
    if (HP_RaceNameHasAny(raceName, {"Giant", "Minotaur", "Cyclops"})) return "Giant";
    if (HP_RaceNameHasAny(raceName, {"Troll", "Ogre"})) return "Giantkin";
    if (HP_RaceNameHasAny(raceName, {"Demon", "Imp", "Gargoyle", "Amygdalan"})) return "Demon";

    // A few classic IDs that benefit from a family icon even when race names
    // are not available or server IDs differ slightly.
    switch (race) {
    case 22: case 81: case 111: return "Insect";
    case 24: case 35: case 63: case 76: case 104: case 105: case 106: case 107: case 112: case 117: case 118: return "Aquatic";
    case 32: case 33: case 46: case 62: case 67: case 72: case 82: case 87: case 100: case 119: case 120: case 124: return "Undead";
    case 34: case 36: case 37: case 38: case 41: case 42: case 43: case 53: case 65: case 78: case 85: case 89: case 93: case 98: case 109: return "Animal";
    case 50: case 91: return "Dragon";
    case 17: case 31: case 55: case 68: case 90: return "Construct";
    case 66: case 28: case 99: return "Plant";
    default: return std::string();
    }
}

static std::string HP_NormalizeIconKey(std::string key)
{
    key = HP_TrimCopy(key);
    std::string out;
    out.reserve(key.size());
    for (char c : key) {
        if ((c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z') || (c >= '0' && c <= '9')) out.push_back(c);
        else if (c == '_' || c == '-') out.push_back('_');
    }
    return out;
}

static std::string HP_MobKeywordIconKey(const std::string& mobName)
{
    std::string direct = HP_MobIconKeyFromAnyText(mobName);
    if (!direct.empty()) return direct;
    std::string n = LowerCopy(mobName);
    struct Rule { const char* find; const char* key; } rules[] = {
        {"sarnak", "Sarnak"}, {"dizok", "Sarnak"}, {"di`zok", "Sarnak"}, {"di_zok", "Sarnak"},
        {"goblin", "Goblin"}, {"orc", "Orc"}, {"human", "Human"}, {"guard", "Guard"},
        {"skeleton", "Undead"}, {"skeletal", "Undead"}, {"undead", "Undead"}, {"zombie", "Undead"},
        {"ghoul", "Undead"}, {"ghost", "Undead"}, {"spectre", "Undead"}, {"wraith", "Undead"},
        {"vampire", "Undead"}, {"lich", "Undead"}, {"mummy", "Undead"},
        {"derasinal", "Dragon"}, {"draazak", "Dragon"}, {"sontalak", "Dragon"},
        {"dragon", "Dragon"}, {"drake", "Dragon"}, {"wyrm", "Dragon"}, {"wyvern", "Dragon"},
        {"giant", "Giant"}, {"cyclops", "Giant"}, {"golem", "Construct"}, {"clockwork", "Construct"},
        {"elemental", "Elemental"}, {"efreet", "Elemental"}, {"froglok", "Froglok"}, {"gnoll", "Gnoll"}, {"kobold", "Kobold"},
        {"spider", "Animal"}, {"wolf", "Animal"}, {"bear", "Animal"}, {"bat", "Animal"}, {"rat", "Animal"},
        {"snake", "Animal"}, {"lion", "Animal"}, {"tiger", "Animal"}, {"puma", "Animal"}, {"cat", "Animal"},
        {"gorilla", "Animal"}, {"mammoth", "Animal"}, {"alligator", "Animal"}, {"lizard", "Animal"},
        {"troll", "Giantkin"}, {"ogre", "Giantkin"}, {"dwarf", "Humanoid"}, {"elf", "Humanoid"},
        {"imp", "Demon"}, {"demon", "Demon"}, {"gargoyle", "Demon"}, {"minotaur", "Giant"},
        {"shark", "Aquatic"}, {"fish", "Aquatic"}, {"eel", "Aquatic"}, {"piranha", "Aquatic"},
        {"beetle", "Insect"}, {"bixie", "Insect"}, {"wasp", "Insect"}, {"bee", "Insect"},
        {"treant", "Plant"}, {"fungus", "Plant"}, {"mushroom", "Plant"}
    };
    for (const auto& r : rules) if (n.find(r.find) != std::string::npos) return r.key;
    return std::string();
}


// MacroQuest spawn structs differ between builds. Some expose Race/BodyType as
// methods, others as fields. The previous icon build only tried GetRace() and
// GetBodyType(); on builds where those helpers do not exist, every mob cached
// as race/body 0 and the fight list fell back to Demon.png even when MQ showed
// Target.Race = Dragon.  These overloads try methods first, then direct fields.
template <typename T>
static auto HP_GetSpawnRaceSafeImpl(T* spawn, int) -> decltype((int)spawn->GetRace())
{
    return spawn ? (int)spawn->GetRace() : 0;
}
template <typename T>
static auto HP_GetSpawnRaceSafeImpl(T* spawn, long) -> decltype((int)spawn->Race)
{
    return spawn ? (int)spawn->Race : 0;
}
static int HP_GetSpawnRaceSafeImpl(...) { return 0; }
static int HP_GetSpawnRaceSafe(PlayerClient* spawn)
{
    return HP_GetSpawnRaceSafeImpl(spawn, 0);
}

template <typename T>
static auto HP_GetSpawnBodyTypeSafeImpl(T* spawn, int) -> decltype((int)spawn->GetBodyType())
{
    return spawn ? (int)spawn->GetBodyType() : 0;
}
template <typename T>
static auto HP_GetSpawnBodyTypeSafeImpl(T* spawn, long) -> decltype((int)spawn->BodyType)
{
    return spawn ? (int)spawn->BodyType : 0;
}
static int HP_GetSpawnBodyTypeSafeImpl(...) { return 0; }
static int HP_GetSpawnBodyTypeSafe(PlayerClient* spawn)
{
    return HP_GetSpawnBodyTypeSafeImpl(spawn, 0);
}

static std::string HP_MobNameMatchKey(std::string s)
{
    s = LowerCopy(HP_TrimCopy(s));
    if (s.rfind("a ", 0) == 0) s = s.substr(2);
    else if (s.rfind("an ", 0) == 0) s = s.substr(3);
    else if (s.rfind("the ", 0) == 0) s = s.substr(4);
    std::string out;
    out.reserve(s.size());
    for (char c : s) {
        if ((c >= 'a' && c <= 'z') || (c >= '0' && c <= '9')) out.push_back(c);
    }
    return out;
}

static bool HP_MobSpawnNameMatches(const std::string& wanted, const char* displayed, const char* rawName)
{
    if (wanted.empty()) return false;
    if (displayed && displayed[0] && wanted == displayed) return true;
    if (rawName && rawName[0] && wanted == rawName) return true;

    // Fallback for servers/builds where DisplayedName contains spacing/articles
    // differently than the combat log. This is only used when a fight starts,
    // not at kill/archive time.
    std::string wantKey = HP_MobNameMatchKey(wanted);
    if (wantKey.empty()) return false;
    if (displayed && displayed[0] && HP_MobNameMatchKey(displayed) == wantKey) return true;
    if (rawName && rawName[0] && HP_MobNameMatchKey(rawName) == wantKey) return true;
    return false;
}

static void HP_SaveMobIconCacheUnlocked()
{
    std::ofstream out(kMobIconCacheFileName, std::ios::out | std::ios::trunc);
    if (!out.good()) return;
    out << "# HealParse Mob Icon Cache v1\n";
    for (const auto& kv : g_mobSpawnInfoCache) {
        if (kv.first.empty()) continue;
        const HP_MobSpawnInfo& mi = kv.second;
        out << HP_EscapeField(kv.first) << '|'
            << mi.race << '|' << mi.bodyType << '|'
            << HP_EscapeField(mi.iconKey) << '|'
            << HP_EscapeField(mi.bodyKey) << '|'
            << HP_EscapeField(mi.raceGroupKey) << '|'
            << mi.lastSeenWall << "\n";
    }
}

static void HP_LoadMobIconCache()
{
    std::ifstream in(kMobIconCacheFileName);
    if (!in.good()) return;

    std::lock_guard<std::mutex> lk(g_mobSpawnInfoCacheMutex);
    std::string line;
    while (std::getline(in, line)) {
        if (line.empty() || line[0] == '#') continue;
        auto parts = HP_SplitEscaped(line);
        if (parts.size() < 4) continue;
        HP_MobSpawnInfo mi;
        mi.race = (int)HP_ParseU64(parts[1]);
        mi.bodyType = (int)HP_ParseU64(parts[2]);
        mi.iconKey = parts[3];
        if (parts.size() >= 5) mi.bodyKey = parts[4];
        if (parts.size() >= 6) mi.raceGroupKey = parts[5];
        if (parts.size() >= 7) mi.lastSeenWall = HP_ParseI64(parts[6]);
        if (mi.bodyKey.empty()) mi.bodyKey = HP_MobBodyTypeIconKey(mi.bodyType);
        if (mi.raceGroupKey.empty()) mi.raceGroupKey = HP_MobRaceGroupIconKey(mi.race, HP_MobRaceNameFromId(mi.race));
        if (!parts[0].empty()) g_mobSpawnInfoCache[LowerCopy(parts[0])] = mi;
    }
}

static void HP_RememberMobSpawnInfo(const std::string& mobName, const HP_MobSpawnInfo& info)
{
    if (mobName.empty()) return;
    if (info.race <= 0 && info.bodyType <= 0 && info.iconKey.empty() && info.bodyKey.empty() && info.raceGroupKey.empty()) return;
    HP_MobSpawnInfo mi = info;
    if (mi.bodyKey.empty()) mi.bodyKey = HP_MobBodyTypeIconKey(mi.bodyType);
    if (mi.raceGroupKey.empty()) mi.raceGroupKey = HP_MobRaceGroupIconKey(mi.race, HP_MobRaceNameFromId(mi.race));
    if (mi.lastSeenWall <= 0) mi.lastSeenWall = HP_WallNow();

    const std::string key = LowerCopy(HP_TrimCopy(mobName));
    if (key.empty()) return;

    std::lock_guard<std::mutex> lk(g_mobSpawnInfoCacheMutex);
    auto it = g_mobSpawnInfoCache.find(key);
    if (it != g_mobSpawnInfoCache.end()
        && it->second.race == mi.race
        && it->second.bodyType == mi.bodyType
        && it->second.iconKey == mi.iconKey
        && it->second.bodyKey == mi.bodyKey
        && it->second.raceGroupKey == mi.raceGroupKey) {
        // Same icon identity; refresh memory only, but do not force a disk save.
        it->second.lastSeenWall = mi.lastSeenWall;
        return;
    }

    g_mobSpawnInfoCache[key] = mi;
    g_mobSpawnInfoCacheDirty.store(true);
}

static HP_MobSpawnInfo HP_GetCachedMobSpawnInfo(const std::string& mobName)
{
    HP_MobSpawnInfo empty;
    std::string key = LowerCopy(HP_TrimCopy(mobName));
    if (key.empty()) return empty;
    std::lock_guard<std::mutex> lk(g_mobSpawnInfoCacheMutex);
    auto it = g_mobSpawnInfoCache.find(key);
    return it == g_mobSpawnInfoCache.end() ? empty : it->second;
}

static std::string HP_EvalMqDataString(const char* expr)
{
    if (!expr || !*expr) return std::string();
    char buf[MAX_STRING] = { 0 };
#ifdef _WIN32
    strncpy_s(buf, expr, _TRUNCATE);
#else
    std::strncpy(buf, expr, sizeof(buf) - 1);
    buf[sizeof(buf) - 1] = '\0';
#endif
    // MacroQuest TLO text is the only reliable source on some custom servers
    // where the C++ spawn numeric Race/Body fields are 0 or server-specific,
    // but ${Target.Race} still prints values like "Vah shir" or "Dragon".
    ParseMacroData(buf, MAX_STRING);
    std::string out = HP_TrimCopy(buf);
    if (out.empty() || out == "NULL" || out == "null" || out == "None") return std::string();
    return out;
}

static bool HP_MobIconKeyIsWeak(const std::string& key)
{
    std::string k = LowerCopy(HP_NormalizeIconKey(key));
    return k.empty() || k == "demon" || k == "monster" || k == "unknown" || k == "humanoid";
}

static HP_MobSpawnInfo HP_GetMobSpawnInfoFromSpawnManager(const std::string& mobName)
{
    HP_MobSpawnInfo info;
    if (mobName.empty()) return info;

    if (pSpawnManager) {
        PlayerClient* best = nullptr;

        // First trust the current EQ target. On Project Lazarus this is often
        // the most reliable place to read Race/Body while the mob is alive,
        // and it avoids missing custom NPCs whose Type is not reported as
        // SPAWN_NPC in the same way as stock EQ.
        if (pTarget) {
            PlayerClient* tgt = (PlayerClient*)pTarget;
            const char* tdn = tgt->DisplayedName;
            const char* tnm = tgt->Name;
            if (HP_MobSpawnNameMatches(mobName, tdn, tnm))
                best = tgt;
        }

        for (PlayerClient* cur = pSpawnManager->FirstSpawn; !best && cur; cur = cur->GetNext()) {
            if (cur->Type == SPAWN_PLAYER) continue;
            const char* dn = cur->DisplayedName;
            const char* nm = cur->Name;
            if (!HP_MobSpawnNameMatches(mobName, dn, nm)) continue;
            best = cur;
            if (cur->MasterID == 0) break; // prefer hostile/non-pet NPC if duplicate names exist
        }

        if (best) {
            info.race = HP_GetSpawnRaceSafe(best);
            info.bodyType = HP_GetSpawnBodyTypeSafe(best);

            const char* raceName = HP_MobRaceNameFromId(info.race);
            std::string mqRaceText;
            std::string mqBodyText;
            if (best == (PlayerClient*)pTarget) {
                mqRaceText = HP_EvalMqDataString("${Target.Race}");
                mqBodyText = HP_EvalMqDataString("${Target.Body}");
            }

            // Across-the-board fix: prefer the same text MacroQuest shows in
            // /echo ${Target.Race}. This catches Project Lazarus/custom mobs
            // such as Race:Vah shir and Race:Dragon even when the numeric C++
            // race/body fields are 0 or do not match stock EQ ids.
            std::string raceTextKey = HP_MobIconKeyFromAnyText(mqRaceText);
            std::string bodyTextKey = HP_MobIconKeyFromAnyText(mqBodyText);

            if (!raceTextKey.empty()) info.iconKey = raceTextKey;
            else if (raceName && raceName[0]) info.iconKey = raceName;

            info.bodyKey = HP_MobBodyTypeIconKey(info.bodyType);
            if (info.bodyKey.empty() && !bodyTextKey.empty()) info.bodyKey = bodyTextKey;

            info.raceGroupKey = HP_MobRaceGroupIconKey(info.race, raceName ? raceName : "");
            if (info.raceGroupKey.empty() && !raceTextKey.empty()) info.raceGroupKey = raceTextKey;
            if (info.raceGroupKey.empty() && !bodyTextKey.empty()) info.raceGroupKey = bodyTextKey;

            // If race/body text indicates a specific family, let that override
            // weak generic values such as Humanoid/Demon/Monster.
            if (HP_MobIconKeyIsWeak(info.iconKey) && !raceTextKey.empty()) info.iconKey = raceTextKey;
            if (HP_MobIconKeyIsWeak(info.iconKey) && !bodyTextKey.empty()) info.iconKey = bodyTextKey;

            if (HP_MobIconIsDragon(info.race, info.bodyType, info.iconKey, mobName)
                || HP_TextLooksLikeDragon(mqRaceText)
                || HP_TextLooksLikeDragon(mqBodyText)) {
                info.iconKey = "Dragon";
                info.raceGroupKey = "Dragon";
            }

            if (info.iconKey.empty()) info.iconKey = info.raceGroupKey;
            if (info.iconKey.empty()) info.iconKey = info.bodyKey;
            if (info.iconKey.empty()) info.iconKey = HP_MobKeywordIconKey(mobName);
            info.lastSeenWall = HP_WallNow();
            HP_RememberMobSpawnInfo(mobName, info);
            return info;
        }
    }

    // Spawn no longer exists. Use the persistent cache from earlier sightings.
    info = HP_GetCachedMobSpawnInfo(mobName);
    if (info.iconKey.empty()) info.iconKey = HP_MobKeywordIconKey(mobName);
    if (info.bodyKey.empty()) info.bodyKey = HP_MobBodyTypeIconKey(info.bodyType);
    if (info.raceGroupKey.empty()) info.raceGroupKey = HP_MobRaceGroupIconKey(info.race, HP_MobRaceNameFromId(info.race));
    return info;
}

static void HP_UpdateLiveMobSpawnInfoLocked()
{
    if (g_liveDps.mob.empty()) return;
    if (g_liveDps.mobRace > 0 && g_liveDps.mobBodyType > 0 && !HP_MobIconKeyIsWeak(g_liveDps.mobIconKey)) return;
    HP_MobSpawnInfo info = HP_GetMobSpawnInfoFromSpawnManager(g_liveDps.mob);
    if (info.race > 0) g_liveDps.mobRace = info.race;
    if (info.bodyType > 0) g_liveDps.mobBodyType = info.bodyType;
    if (!HP_MobIconKeyIsWeak(info.iconKey) || HP_MobIconKeyIsWeak(g_liveDps.mobIconKey)) g_liveDps.mobIconKey = info.iconKey;
}

static HP_MobSpawnInfo HP_GetMobSpawnInfoNoScan(const std::string& mobName)
{
    HP_MobSpawnInfo info = HP_GetCachedMobSpawnInfo(mobName);
    if (info.iconKey.empty()) info.iconKey = HP_MobKeywordIconKey(mobName);
    if (info.bodyKey.empty()) info.bodyKey = HP_MobBodyTypeIconKey(info.bodyType);
    if (info.raceGroupKey.empty()) info.raceGroupKey = HP_MobRaceGroupIconKey(info.race, HP_MobRaceNameFromId(info.race));
    return info;
}

static void HP_SaveMobIconCacheIfDirty()
{
    if (!g_mobSpawnInfoCacheDirty.exchange(false)) return;
    std::lock_guard<std::mutex> mk(g_mobSpawnInfoCacheMutex);
    HP_SaveMobIconCacheUnlocked();
}


static std::string HP_FormatDateTimeLong(int64_t wall)
{
    if (wall <= 0) return "Unknown";
    std::time_t t = static_cast<std::time_t>(wall);
    std::tm tmv{};
#ifdef _WIN32
    localtime_s(&tmv, &t);
#else
    localtime_r(&t, &tmv);
#endif
    char buf[64] = {0};
    std::strftime(buf, sizeof(buf), "%B %d, %Y %I:%M %p", &tmv);
    return buf;
}

static bool HP_FightMatchesDateFilter(const CompletedDpsFight& f)
{
    std::string d = HP_FormatDateOnly(f.wallEnded > 0 ? f.wallEnded : f.wallStarted);
    if (d == "Unknown") return true;

    // Default fight list behavior: only show today's fights when no date
    // filter is selected. The From/To filter below is still used to pull up
    // older fights on demand.
    if (!g_dpsDateFrom[0] && !g_dpsDateTo[0]) {
        const std::string today = HP_FormatDateOnly(HP_WallNow());
        return d == today;
    }

    if (g_dpsDateFrom[0] && d < std::string(g_dpsDateFrom)) return false;
    if (g_dpsDateTo[0] && d > std::string(g_dpsDateTo)) return false;
    return true;
}

static bool HP_FightMatchesDurationFilter(const CompletedDpsFight& f)
{
    int fdur = (int)std::max<int64_t>(1, (f.endedMs - f.startedMs) / 1000);
    switch (g_dpsDurationFilter) {
    case 1: return fdur < 30;
    case 2: return fdur >= 30 && fdur < 60;
    case 3: return fdur >= 60 && fdur < 120;
    case 4: return fdur >= 120;
    default: return true;
    }
}

static bool HP_FightPassesDpsFilters(const CompletedDpsFight& f)
{
    if (HP_IsInvalidFightTargetName(f.mob)) return false;
    if (g_dpsMinDamageFilter > 0 && f.total < (uint64_t)g_dpsMinDamageFilter) return false;
    if (!HP_ContainsNoCase(f.mob, g_dpsMobSearch)) return false;
    if (!HP_FightMatchesDateFilter(f)) return false;
    if (!HP_FightMatchesDurationFilter(f)) return false;
    return true;
}

static void HP_SaveDpsHistoryUnlocked()
{
    std::ofstream out(kDpsHistoryFileName, std::ios::out | std::ios::trunc);
    if (!out.good()) return;
    out << "# HealParse DPS History v3\n";
    for (const auto& f : g_completedDpsFights) {
        out << "F|" << HP_EscapeField(f.mob) << '|' << f.startedMs << '|' << f.endedMs << '|' << f.total << '|' << f.wallStarted << '|' << f.wallEnded
            << '|' << f.mobRace << '|' << f.mobBodyType << '|' << HP_EscapeField(f.mobIconKey) << "\n";
        for (const auto& kv : f.players) {
            const auto& r = kv.second;
            out << "P|" << HP_EscapeField(kv.first)
                << '|' << r.total << '|' << r.melee << '|' << r.spell << '|' << r.dot
                << '|' << r.proc << '|' << r.pet << '|' << r.swarm << '|' << r.other
                << '|' << r.count << '|' << r.maxHit << '|' << r.maxHitWall << "\n";
        }
        for (const auto& skv : f.spellCasts) {
            if (!skv.first.empty() && skv.second > 0)
                out << "S|" << HP_EscapeField(skv.first) << '|' << skv.second << "\n";
        }
        // Persist caster -> spell breakdown for the View All Spells popup.
        for (const auto& ckv : f.spellCastsByCaster) {
            if (ckv.first.empty()) continue;
            for (const auto& skv : ckv.second) {
                if (!skv.first.empty() && skv.second > 0)
                    out << "C|" << HP_EscapeField(ckv.first) << '|' << HP_EscapeField(skv.first) << '|' << skv.second << "\n";
            }
        }
        // Persist per-fight DPS spike events so the View All DPS Spikes popup
        // keeps exact timestamps after a plugin rebuild/update.
        for (const auto& sp : f.dpsSpikes) {
            out << "K|" << HP_EscapeField(sp.player)
                << '|' << HP_EscapeField(sp.target)
                << '|' << HP_EscapeField(sp.type)
                << '|' << sp.amount << '|' << sp.ms << '|' << sp.wall << "\n";
        }
        for (const auto& d : f.deaths) {
            out << "D|" << HP_EscapeField(d.player) << '|' << HP_EscapeField(d.killer)
                << '|' << d.ms << '|' << d.wall << '|' << d.recentDamage << "\n";
        }
        for (const auto& line : f.logs) {
            out << "L|" << HP_EscapeField(line) << "\n";
        }
        out << "E\n";
    }
}

static void HP_LoadDpsHistory()
{
    std::ifstream in(kDpsHistoryFileName);
    if (!in.good()) return;

    std::vector<CompletedDpsFight> loaded;
    CompletedDpsFight cur;
    bool have = false;
    std::string line;
    while (std::getline(in, line)) {
        if (line.empty() || line[0] == '#') continue;
        auto parts = HP_SplitEscaped(line);
        if (parts.empty()) continue;
        if (parts[0] == "F" && parts.size() >= 5) {
            if (have && !cur.mob.empty() && cur.total > 0)
                loaded.push_back(cur);
            cur = CompletedDpsFight{};
            cur.mob = parts[1];
            cur.startedMs = HP_ParseI64(parts[2]);
            cur.endedMs = HP_ParseI64(parts[3]);
            cur.total = HP_ParseU64(parts[4]);
            if (parts.size() >= 7) {
                cur.wallStarted = HP_ParseI64(parts[5]);
                cur.wallEnded = HP_ParseI64(parts[6]);
            }
            if (parts.size() >= 10) {
                cur.mobRace = (int)HP_ParseU64(parts[7]);
                cur.mobBodyType = (int)HP_ParseU64(parts[8]);
                cur.mobIconKey = parts[9];
            } else {
                cur.mobIconKey = HP_MobKeywordIconKey(cur.mob);
            }
            have = true;
        } else if (parts[0] == "P" && have && parts.size() >= 12) {
            LiveDpsRow r;
            r.total = HP_ParseU64(parts[2]);
            r.melee = HP_ParseU64(parts[3]);
            r.spell = HP_ParseU64(parts[4]);
            r.dot = HP_ParseU64(parts[5]);
            r.proc = HP_ParseU64(parts[6]);
            r.pet = HP_ParseU64(parts[7]);
            r.swarm = HP_ParseU64(parts[8]);
            r.other = HP_ParseU64(parts[9]);
            r.count = static_cast<uint32_t>(HP_ParseU64(parts[10]));
            r.maxHit = static_cast<uint32_t>(HP_ParseU64(parts[11]));
            if (parts.size() >= 13) r.maxHitWall = HP_ParseI64(parts[12]);
            cur.players[parts[1]] = r;
        } else if (parts[0] == "S" && have && parts.size() >= 3) {
            cur.spellCasts[parts[1]] += static_cast<uint32_t>(HP_ParseU64(parts[2]));
        } else if (parts[0] == "C" && have && parts.size() >= 4) {
            const uint32_t casts = static_cast<uint32_t>(HP_ParseU64(parts[3]));
            if (!parts[1].empty() && !parts[2].empty() && casts > 0)
                cur.spellCastsByCaster[parts[1]][parts[2]] += casts;
        } else if (parts[0] == "K" && have && parts.size() >= 7) {
            HP_DpsSpikeEvent sp;
            sp.player = parts[1];
            sp.target = parts[2];
            sp.type = parts[3];
            sp.amount = HP_ParseU64(parts[4]);
            sp.ms = HP_ParseI64(parts[5]);
            sp.wall = HP_ParseI64(parts[6]);
            if (!sp.player.empty() && sp.amount > 0)
                cur.dpsSpikes.push_back(std::move(sp));
        } else if (parts[0] == "D" && have && parts.size() >= 6) {
            HPPcDeathRow d;
            d.player = parts[1];
            d.killer = parts[2];
            d.ms = HP_ParseI64(parts[3]);
            d.wall = HP_ParseI64(parts[4]);
            d.recentDamage = HP_ParseU64(parts[5]);
            cur.deaths.push_back(d);
        } else if (parts[0] == "L" && have && parts.size() >= 2) {
            cur.logs.push_back(parts[1]);
        } else if (parts[0] == "E" && have) {
            if (!cur.mob.empty() && cur.total > 0)
                loaded.push_back(cur);
            cur = CompletedDpsFight{};
            have = false;
        }
    }
    if (have && !cur.mob.empty() && cur.total > 0)
        loaded.push_back(cur);

    if (loaded.empty()) return;
    if (loaded.size() > kMaxCompletedDpsFights)
        loaded.resize(kMaxCompletedDpsFights);

    std::lock_guard<std::mutex> hk(g_completedDpsMutex);
    g_completedDpsFights = std::move(loaded);
    if (!g_completedDpsFights.empty() && g_fullUiDpsSelectedFight.load() < 0)
        g_fullUiDpsSelectedFight.store(0);
}

static bool HP_ContainsNoCase(const std::string& hay, const char* needle)
{
    if (!needle || !needle[0]) return true;
    std::string h = hay;
    std::string n = needle;
    std::transform(h.begin(), h.end(), h.begin(), [](unsigned char c){ return (char)std::tolower(c); });
    std::transform(n.begin(), n.end(), n.begin(), [](unsigned char c){ return (char)std::tolower(c); });
    return h.find(n) != std::string::npos;
}

static void HP_ArchiveLiveTankForFight(const CompletedDpsFight& f, const char* reason);
static void HP_ArchiveLiveHealsForFight(const CompletedDpsFight& f);

static void HP_ArchiveLiveDpsLocked(const char* reason)
{
    if (g_liveDps.mob.empty() || g_liveDps.total == 0 || g_liveDps.players.empty()) return;

    CompletedDpsFight f;
    f.mob = g_liveDps.mob;
    f.mobRace = g_liveDps.mobRace;
    f.mobBodyType = g_liveDps.mobBodyType;
    f.mobIconKey = g_liveDps.mobIconKey;

    // Important performance rule: do not walk pSpawnManager at kill/archive
    // time.  The spawn may already be despawning and the UI is about to redraw,
    // so archive only uses info captured at fight start/during live damage,
    // with a cheap persistent-cache/keyword fallback.
    if (f.mobRace <= 0 && f.mobBodyType <= 0 && f.mobIconKey.empty()) {
        HP_MobSpawnInfo mi = HP_GetMobSpawnInfoNoScan(f.mob);
        f.mobRace = mi.race;
        f.mobBodyType = mi.bodyType;
        f.mobIconKey = mi.iconKey;
    }
    f.startedMs = g_liveDps.startedMs;
    f.endedMs = NowMs();
    f.wallStarted = g_liveDps.wallStarted;
    f.wallEnded = HP_WallNow();
    if (f.wallStarted <= 0) {
        int64_t durSec = std::max<int64_t>(1, (f.endedMs - f.startedMs) / 1000);
        f.wallStarted = f.wallEnded - durSec;
    }
    f.total = g_liveDps.total;
    f.players = g_liveDps.players;
    f.deaths = g_liveDps.deaths;
    f.logs = g_liveDps.logs;
    f.dpsSpikes = g_liveDps.dpsSpikes;
    f.spellCasts = g_liveDps.spellCasts;
    f.spellCastsByCaster = g_liveDps.spellCastsByCaster;

    {
        std::lock_guard<std::mutex> hk(g_completedDpsMutex);
        // Guard against duplicate slain/timeout paths saving the same fight twice.
        if (!g_completedDpsFights.empty()) {
            const auto& last = g_completedDpsFights.front();
            long long deltaMs = (long long)(last.endedMs - f.endedMs);
            if (deltaMs < 0) deltaMs = -deltaMs;
            if (last.mob == f.mob && last.total == f.total && deltaMs < 1500)
                return;
        }
        // Only show the after-fight popup if the user has opened/enabled the UI.
        // This keeps boxed alts from popping HealTracker windows just because the
        // plugin is loaded and parsing in the background.
        if (g_enableAfterFightPopup.load() && (g_fullUiEnabled.load() || g_liveOverlayEnabled.load())) {
            std::lock_guard<std::mutex> pk(g_afterFightPopupMutex);
            g_afterFightPopup = f;
            g_afterFightPopupOpen.store(true);
            g_afterFightPopupShownMs.store(NowMs());
            g_liveOverlayForceVisible.store(true);
        }

        HP_ArchiveLiveTankForFight(f, reason);
        HP_ArchiveLiveHealsForFight(f);

        g_completedDpsFights.insert(g_completedDpsFights.begin(), std::move(f));
        if (g_completedDpsFights.size() > kMaxCompletedDpsFights)
            g_completedDpsFights.resize(kMaxCompletedDpsFights);

        // Do not write DPS history here. This function runs directly after a
        // kill/timeout/new-target, and rewriting the full history file here
        // causes a visible hitch.  Mark dirty and let OnPulse save later.
        g_dpsHistoryDirty.store(true);
        g_historyDirtyAtMs.store(NowMs());
        // Mob icon cache is saved later/on shutdown only when dirty.  Do not
        // write it here; this function runs at kill/new-target/timeout archive
        // time and disk I/O here caused visible hitches.
    }

    if (g_debug.load())
        WriteChatf("\ag[HealParse]\ax archived DPS fight (%s): %s", reason ? reason : "end", g_liveDps.mob.c_str());
}

static void HP_ClearLiveTankRows();

static void HP_ClearLiveDpsLocked()
{
    g_liveDps = LiveDpsFight{};
    // Do NOT clear tank rows here. Incoming tank data can arrive on a slightly
    // different cadence than outgoing DPS, and clearing it at the exact DPS
    // timeout made the Tank tab look like it never parsed anything after a
    // despawn/timeout fight. Tank rows now use their own stale timeout below.
    // Keep the DPS page focused on the newest archived fight when one exists.
    // If there are no saved fights yet, fall back to the live/current row.
    {
        std::lock_guard<std::mutex> hk(g_completedDpsMutex);
        g_fullUiDpsSelectedFight.store(g_completedDpsFights.empty() ? -1 : 0);
    }
}

std::string g_fullUiDpsSelectedPlayer;
constexpr int64_t kLiveDpsTimeoutMs = 10000;

static void HP_MaybeArchiveTimedOutLiveDps()
{
    const int64_t now = NowMs();
    std::lock_guard<std::mutex> lk(g_liveDpsMutex);
    if (!g_liveDps.mob.empty() && g_liveDps.total > 0 && (now - g_liveDps.lastDamageMs) > kLiveDpsTimeoutMs) {
        HP_ArchiveLiveDpsLocked("timeout");
        HP_ClearLiveDpsLocked();
    }
}

static void HP_ImportRecentDpsSpellCastsLocked(int64_t now)
{
    std::lock_guard<std::mutex> pk(g_pendingDpsSpellMutex);
    for (const auto& pc : g_pendingDpsSpellCasts) {
        if (!pc.spell.empty() && !pc.caster.empty() && (now - pc.ms) <= 15000) {
            g_liveDps.spellCasts[pc.spell] += 1;
            g_liveDps.spellCastsByCaster[pc.caster][pc.spell] += 1;
        }
    }
    g_pendingDpsSpellCasts.clear();
}

static void HP_BumpDamageType(LiveDpsRow& r, const std::string& type, uint64_t amount)
{
    std::string t = type;
    std::transform(t.begin(), t.end(), t.begin(), [](unsigned char c) { return (char)std::tolower(c); });
    if (t == "melee") r.melee += amount;
    else if (t == "dot" || t == "disease" || t == "poison") r.dot += amount;
    else if (t == "proc") r.proc += amount;
    else if (t == "pet") r.pet += amount;
    else if (t == "swarm" || t == "swarmpet" || t == "swarm_pet") r.swarm += amount;
    else if (t == "spell" || t == "nonmelee" || t == "non-melee" || t == "nuke") r.spell += amount;
    else r.other += amount;
}

void NoteLiveDamage(const std::string& attacker, const std::string& target, uint64_t amount, uint32_t maxHit, const std::string& type = "melee")
{
    if (attacker.empty() || target.empty() || amount == 0) return;
    if (HP_IsInvalidFightTargetName(target)) return;

    // DPS rows are for player/pet damage done TO the mob. If the mob name
    // leaks in as an attacker, do not record it as a Player Damage row.
    if (HP_SameNameNoCase(attacker, target)) return;
    if (HP_ShouldHideDpsDisplayRow(attacker, target)) return;

    const int64_t now = NowMs();
    std::lock_guard<std::mutex> lk(g_liveDpsMutex);
    if (!g_liveDps.mob.empty() && HP_SameNameNoCase(attacker, g_liveDps.mob)) return;

    if (g_liveDps.mob.empty()
        || (now - g_liveDps.lastDamageMs) > kLiveDpsTimeoutMs
        || (!HP_SameNameNoCase(target, g_liveDps.mob) && amount > g_liveDps.total)) {
        if (!g_liveDps.mob.empty() && g_liveDps.total > 0)
            HP_ArchiveLiveDpsLocked((now - g_liveDps.lastDamageMs) > kLiveDpsTimeoutMs ? "timeout" : "new-target");
        g_liveDps = LiveDpsFight{};
        g_liveDps.mob = target;
        {
            HP_MobSpawnInfo mi = HP_GetMobSpawnInfoFromSpawnManager(target);
            g_liveDps.mobRace = mi.race;
            g_liveDps.mobBodyType = mi.bodyType;
            g_liveDps.mobIconKey = mi.iconKey;
        }
        g_liveDps.startedMs = now;
        g_liveDps.wallStarted = HP_WallNow();
        HP_ImportRecentDpsSpellCastsLocked(now);
        g_fullUiDpsSelectedFight.store(-1);
    }

    // Accuracy fix:
    // GamParse's selected fight only includes damage done to that selected NPC.
    // Rain spells and AE spells can hit nearby adds such as "an iron warder" or
    // "a granite defender". The old plugin kept those hits inside the current
    // visible fight, which made wizards/enchanters look higher than GamParse.
    // Keep the current fight stable, but DROP off-target damage from its totals.
    if (!HP_SameNameNoCase(target, g_liveDps.mob) && g_liveDps.total > 0) {
        HP_AuditLine("DROP", attacker, HP_GetLinkedPetOwnerForDisplay(attacker), target, amount, type, std::string(), "off-target-live-fight");
        return;
    }

    HP_UpdateLiveMobSpawnInfoLocked();
    g_liveDps.lastDamageMs = now;
    g_liveDps.total += amount;
    HP_DpsSpikeEvent sev;
    sev.player = attacker;
    sev.target = target;
    sev.type = type;
    sev.amount = amount;
    sev.ms = now;
    sev.wall = HP_WallNow();
    g_liveDps.dpsSpikes.push_back(sev);
    if (g_liveDps.dpsSpikes.size() > 12000)
        g_liveDps.dpsSpikes.erase(g_liveDps.dpsSpikes.begin(), g_liveDps.dpsSpikes.begin() + (g_liveDps.dpsSpikes.size() - 12000));
    auto& r = g_liveDps.players[attacker];
    r.total += amount;
    HP_BumpDamageType(r, type, amount);
    r.count += 1;
    if (maxHit > r.maxHit) {
        r.maxHit = maxHit;
        r.maxHitWall = HP_WallNow();
    }
}


static bool HP_LiveDpsHasPlayerNoLock(const std::string& name)
{
    if (name.empty()) return false;
    if (g_liveDps.players.find(name) != g_liveDps.players.end()) return true;
    return false;
}

static void HP_NotePcDeath(const std::string& player, const std::string& killer)
{
    if (player.empty()) return;
    const int64_t now = NowMs();
    std::lock_guard<std::mutex> lk(g_liveDpsMutex);
    if (g_liveDps.mob.empty() || g_liveDps.total == 0) return;

    for (const auto& d : g_liveDps.deaths) {
        if (d.player == player && (now - d.ms) >= 0 && (now - d.ms) < 2500) return;
    }

    HPPcDeathRow d;
    d.player = player;
    d.killer = killer.empty() ? g_liveDps.mob : killer;
    d.ms = now;
    d.wall = HP_WallNow();
    d.recentDamage = 0;
    g_liveDps.deaths.push_back(d);
    if (g_liveDps.deaths.size() > 32)
        g_liveDps.deaths.erase(g_liveDps.deaths.begin(), g_liveDps.deaths.begin() + (g_liveDps.deaths.size() - 32));
}

// ----------------------------------------------------------------------------
// Live HEALS leaderboard. Mirrors the live DPS fight but keyed by healer. Fed
// from the single BumpHeal() choke point so it costs one map bump per heal.
// ----------------------------------------------------------------------------
struct LiveHealRow {
    uint64_t total = 0;
    uint32_t count = 0;
    uint32_t maxHeal = 0;
};

static std::string HP_NormalizeHealCasterName(std::string healer);

struct LiveHealDetailRow {
    std::string type;
    std::string name;
    std::string caster;
    std::string target;
    uint32_t amount = 0;
    int64_t wall = 0;
};

struct LiveHealFight {
    std::string mob;
    int64_t startedMs = 0;
    int64_t lastHealMs = 0;
    uint64_t total = 0;
    std::unordered_map<std::string, LiveHealRow> healers;
    std::unordered_map<std::string, LiveHealRow> targets;
    std::unordered_map<std::string, LiveHealRow> spells;
    std::vector<LiveHealDetailRow> details;
};

LiveHealFight g_liveHeals;
std::mutex g_liveHealsMutex;
std::vector<LiveHealFight> g_completedHealFights;
std::mutex g_completedHealFightsMutex;

static void HP_SaveHealHistoryUnlocked()
{
    std::ofstream out(kHealHistoryFileName, std::ios::out | std::ios::trunc);
    if (!out.good()) return;
    out << "# HealParse Heal History v1\n";
    for (const auto& f : g_completedHealFights) {
        out << "F|" << HP_EscapeField(f.mob) << '|' << f.startedMs << '|' << f.lastHealMs << '|' << f.total << "\n";
        for (const auto& kv : f.healers) {
            const auto& r = kv.second;
            out << "H|" << HP_EscapeField(kv.first) << '|' << r.total << '|' << r.count << '|' << r.maxHeal << "\n";
        }
        for (const auto& kv : f.targets) {
            const auto& r = kv.second;
            out << "T|" << HP_EscapeField(kv.first) << '|' << r.total << '|' << r.count << '|' << r.maxHeal << "\n";
        }
        for (const auto& kv : f.spells) {
            const auto& r = kv.second;
            out << "S|" << HP_EscapeField(kv.first) << '|' << r.total << '|' << r.count << '|' << r.maxHeal << "\n";
        }
        for (const auto& d : f.details) {
            out << "R|" << HP_EscapeField(d.type) << '|' << HP_EscapeField(d.name) << '|'
                << HP_EscapeField(d.caster) << '|' << HP_EscapeField(d.target) << '|'
                << d.amount << '|' << d.wall << "\n";
        }
        out << "E\n";
    }
}

static void HP_LoadHealHistory()
{
    std::ifstream in(kHealHistoryFileName);
    if (!in.good()) return;

    std::vector<LiveHealFight> loaded;
    LiveHealFight cur;
    bool have = false;
    std::string line;
    while (std::getline(in, line)) {
        if (line.empty() || line[0] == '#') continue;
        auto parts = HP_SplitEscaped(line);
        if (parts.empty()) continue;
        if (parts[0] == "F" && parts.size() >= 5) {
            if (have && !cur.mob.empty()) loaded.push_back(cur);
            cur = LiveHealFight{};
            cur.mob = parts[1];
            cur.startedMs = HP_ParseI64(parts[2]);
            cur.lastHealMs = HP_ParseI64(parts[3]);
            cur.total = HP_ParseU64(parts[4]);
            have = true;
        } else if ((parts[0] == "H" || parts[0] == "T" || parts[0] == "S") && have && parts.size() >= 5) {
            LiveHealRow r;
            r.total = HP_ParseU64(parts[2]);
            r.count = static_cast<uint32_t>(HP_ParseU64(parts[3]));
            r.maxHeal = static_cast<uint32_t>(HP_ParseU64(parts[4]));
            if (parts[0] == "H") cur.healers[parts[1]] = r;
            else if (parts[0] == "T") cur.targets[parts[1]] = r;
            else cur.spells[parts[1]] = r;
        } else if (parts[0] == "R" && have && parts.size() >= 7) {
            LiveHealDetailRow d;
            d.type = parts[1];
            d.name = parts[2];
            d.caster = HP_NormalizeHealCasterName(parts[3]);
            d.target = parts[4];
            d.amount = static_cast<uint32_t>(HP_ParseU64(parts[5]));
            d.wall = HP_ParseI64(parts[6]);
            cur.details.push_back(d);
        } else if (parts[0] == "E" && have) {
            loaded.push_back(cur);
            cur = LiveHealFight{};
            have = false;
        }
    }
    if (have && !cur.mob.empty()) loaded.push_back(cur);
    if (loaded.size() > kMaxCompletedDpsFights) loaded.resize(kMaxCompletedDpsFights);

    std::lock_guard<std::mutex> hk(g_completedHealFightsMutex);
    g_completedHealFights = std::move(loaded);
}

static void HP_ArchiveLiveHealsForFight(const CompletedDpsFight& f)
{
    LiveHealFight snap;
    {
        std::lock_guard<std::mutex> lk(g_liveHealsMutex);
        if (!g_liveHeals.mob.empty() && HP_SameNameNoCase(g_liveHeals.mob, f.mob) && g_liveHeals.total > 0) {
            snap = g_liveHeals;
            if (snap.startedMs <= 0) snap.startedMs = f.startedMs;
            if (snap.lastHealMs <= 0) snap.lastHealMs = f.endedMs;
        } else {
            snap.mob = f.mob;
            snap.startedMs = f.startedMs;
            snap.lastHealMs = f.endedMs;
        }

        // Important: once DPS archives a fight, freeze the healing snapshot for
        // that fight and clear live heals. This prevents the next selected fight
        // from reusing or accumulating the previous fight's healing totals.
        if (HP_SameNameNoCase(g_liveHeals.mob, f.mob))
            g_liveHeals = LiveHealFight{};
    }

    std::lock_guard<std::mutex> hk(g_completedHealFightsMutex);
    g_completedHealFights.insert(g_completedHealFights.begin(), std::move(snap));
    if (g_completedHealFights.size() > kMaxCompletedDpsFights)
        g_completedHealFights.resize(kMaxCompletedDpsFights);

    // Do not write heal history at kill/archive time.  Mark dirty and defer
    // disk I/O so the kill event remains smooth.
    g_healHistoryDirty.store(true);
    g_historyDirtyAtMs.store(NowMs());
}

static void HP_BumpLiveHealRow(LiveHealRow& r, uint32_t amount)
{
    r.total += amount;
    r.count += 1;
    if (amount > r.maxHeal) r.maxHeal = amount;
}

static bool HP_IsRuneOrProcHealName(const std::string& name)
{
    std::string n = LowerCopy(name);
    return n.find("rune") != std::string::npos
        || n.find("glyph") != std::string::npos
        || n.find("aspect of survival") != std::string::npos
        || n.find("self-proc") != std::string::npos
        || n.find("proc") != std::string::npos
        || n.find("shield") != std::string::npos;
}

static bool HP_IsHotRegenHealName(const std::string& name)
{
    std::string n = LowerCopy(name);
    Trim(n);
    return n.find("hot") != std::string::npos
        || n.find("regen") != std::string::npos
        || n.find("regeneration") != std::string::npos
        || n.find("pious elixir") != std::string::npos
        || n.find("celestial regeneration") != std::string::npos
        || n.find("transcendent torpor") != std::string::npos;
}

static std::string HP_ExtractHealSpellFromTail(const char* tail)
{
    if (!tail || !*tail) return {};

    // Common EQ heal form:
    //   "... hit points by Pious Elixir."
    //   "... hit points by Celestial Regeneration."
    // We only extract the effect/spell name after the final " by ".
    const char* by = FindSubstr(tail, " by ");
    if (!by) return {};

    std::string spell = by + 4;
    Trim(spell);
    if (spell.empty()) return {};

    if (IStartsWith(spell.c_str(), "your "))
        spell.erase(0, 5);

    // Stop at sentence punctuation or extra log text.
    size_t cut = spell.find_first_of(".!");
    if (cut != std::string::npos) spell.erase(cut);
    Trim(spell);
    return spell;
}

static std::string HP_GetLocalPlayerNameForHeals()
{
    if (auto pChar = GetCharInfo()) {
        if (pChar->Name[0])
            return pChar->Name;
    }
    return {};
}

static std::string HP_NormalizeHealCasterName(std::string healer)
{
    Trim(healer);
    std::string h = LowerCopy(healer);
    Trim(h);

    // EQ self-cast heal lines are written as: "You have healed <target> for ...".
    // If a generic parser catches that line first, the text before " healed "
    // becomes "You have".  Normalize that to the actual character name so
    // spike detail popups show "Dorfus" instead of "You have".
    if (h == "you" || h == "you have" || h == "you've") {
        std::string me = HP_GetLocalPlayerNameForHeals();
        if (!me.empty()) return me;
    }
    return healer;
}

void NoteLiveHeal(const std::string& target, const std::string& healer, const std::string& spellName, const std::string& healType, uint32_t amount)
{
    if (amount == 0) return;
    const int64_t now = NowMs();
    std::string cleanTarget = target.empty() ? "Unknown" : target;
    std::string cleanHealer = HP_NormalizeHealCasterName(healer.empty() ? cleanTarget : healer);
    std::string cleanSpell = spellName.empty() ? "Direct Heals" : spellName;
    std::string cleanType = healType.empty() ? "Heal" : healType;

    // Only count healing while an actual DPS fight is active. This prevents
    // raid HPS / your HPS from continuing to drift downward from out-of-combat
    // heals after the fight has ended.
    std::string activeMob;
    int64_t activeFightStartMs = 0;
    {
        std::lock_guard<std::mutex> dlk(g_liveDpsMutex);
        if (g_liveDps.mob.empty() || g_liveDps.total == 0 || (now - g_liveDps.lastDamageMs) > kLiveDpsTimeoutMs)
            return;
        activeMob = g_liveDps.mob;
        activeFightStartMs = g_liveDps.startedMs;
    }

    std::lock_guard<std::mutex> lk(g_liveHealsMutex);

    // Reset healing when the DPS fight changes. Tie healing duration to the
    // combat window, not to how long the UI has been open.
    if (g_liveHeals.startedMs == 0
        || g_liveHeals.mob != activeMob
        || (now - g_liveHeals.lastHealMs) > kLiveDpsTimeoutMs) {
        g_liveHeals = LiveHealFight{};
        g_liveHeals.mob = activeMob;
        g_liveHeals.startedMs = activeFightStartMs > 0 ? activeFightStartMs : now;
    }

    g_liveHeals.lastHealMs = now;
    g_liveHeals.total += amount;
    HP_BumpLiveHealRow(g_liveHeals.healers[cleanHealer], amount);
    HP_BumpLiveHealRow(g_liveHeals.targets[cleanTarget], amount);
    HP_BumpLiveHealRow(g_liveHeals.spells[cleanSpell], amount);

    // Keep every heal event with caster and target so the Heals tab can show
    // HEALED FOR by recipient and who healed them. The Rune/Proc panel filters
    // this same detail list down to rune/proc rows only.
    {
        LiveHealDetailRow d;
        d.type = cleanType;
        d.name = cleanSpell;
        d.caster = cleanHealer;
        d.target = cleanTarget;
        d.amount = amount;
        d.wall = HP_WallNow();
        g_liveHeals.details.push_back(std::move(d));
        if (g_liveHeals.details.size() > 5000)
            g_liveHeals.details.erase(g_liveHeals.details.begin(), g_liveHeals.details.begin() + (g_liveHeals.details.size() - 5000));
    }
}

void NoteLiveHeal(const std::string& healer, uint32_t amount)
{
    NoteLiveHeal(std::string(), healer, std::string("Direct Heals"), std::string("Heal"), amount);
}

// ----------------------------------------------------------------------------
// Live tank/avoidance snapshot for the plugin UI.
// ----------------------------------------------------------------------------
struct LiveTankHitEvent {
    int64_t ms = 0;
    uint32_t amount = 0;
    std::string attacker;
    std::string type;
};

struct LiveTankRow {
    uint64_t damage = 0;
    uint32_t hits = 0;
    uint32_t maxHit = 0;
    uint32_t misses = 0;
    uint32_t dodges = 0;
    uint32_t parries = 0;
    uint32_t ripostes = 0;
    uint32_t blocks = 0;
    int64_t firstMs = 0;
    int64_t lastMs = 0;
    std::vector<LiveTankHitEvent> hitEvents;
    std::vector<LiveTankHitEvent> lastHits;
};

static uint64_t HP_TankSwings(const LiveTankRow& t)
{
    return (uint64_t)t.hits + t.misses + t.dodges + t.parries + t.ripostes + t.blocks;
}

static uint32_t HP_TankAvoided(const LiveTankRow& t)
{
    return t.misses + t.dodges + t.parries + t.ripostes + t.blocks;
}

static uint64_t HP_TankWorstSpike3s(const LiveTankRow& t)
{
    uint64_t best = 0;
    const auto& ev = t.hitEvents;
    for (size_t i = 0; i < ev.size(); ++i) {
        uint64_t sum = 0;
        const int64_t start = ev[i].ms;
        for (size_t j = i; j < ev.size(); ++j) {
            if ((ev[j].ms - start) > 3000) break;
            sum += ev[j].amount;
        }
        if (sum > best) best = sum;
    }
    return best;
}

std::unordered_map<std::string, LiveTankRow> g_liveTank;
std::mutex g_liveTankMutex;

struct CompletedTankFight {
    std::string mob;
    int64_t startedMs = 0;
    int64_t endedMs = 0;
    uint64_t total = 0;
    std::unordered_map<std::string, LiveTankRow> tanks;
};

std::vector<CompletedTankFight> g_completedTankFights;
std::mutex g_completedTankMutex;
std::atomic<int> g_fullUiTankSelectedFight{ -1 }; // -1 = active/live tank; >=0 completed tank fight index
constexpr size_t kMaxCompletedTankFights = 300;
std::string g_fullUiTankSelectedPlayer;

static void HP_ArchiveLiveTankForFight(const CompletedDpsFight& dpsFight, const char* reason)
{
    CompletedTankFight tf;
    tf.mob = dpsFight.mob.empty() ? std::string("Unknown fight") : dpsFight.mob;
    tf.startedMs = dpsFight.startedMs;
    tf.endedMs = dpsFight.endedMs ? dpsFight.endedMs : NowMs();

    {
        std::lock_guard<std::mutex> lk(g_liveTankMutex);
        if (g_liveTank.empty()) return;
        tf.tanks = g_liveTank;
        for (const auto& kv : tf.tanks)
            tf.total += kv.second.damage;
    }

    if (tf.total == 0 && tf.tanks.empty()) return;

    std::lock_guard<std::mutex> hk(g_completedTankMutex);
    if (!g_completedTankFights.empty()) {
        const auto& last = g_completedTankFights.front();
        long long deltaMs = (long long)(last.endedMs - tf.endedMs);
        if (deltaMs < 0) deltaMs = -deltaMs;
        if (last.mob == tf.mob && last.total == tf.total && deltaMs < 1500)
            return;
    }

    g_completedTankFights.insert(g_completedTankFights.begin(), std::move(tf));
    if (g_completedTankFights.size() > kMaxCompletedTankFights)
        g_completedTankFights.resize(kMaxCompletedTankFights);
    g_fullUiTankSelectedFight.store(0);
    if (g_debug.load())
        WriteChatf("\ag[HealParse]\ax archived Tank fight (%s): %s", reason ? reason : "end", dpsFight.mob.c_str());
}

static void HP_ClearLiveTankRows()
{
    std::lock_guard<std::mutex> tk(g_liveTankMutex);
    g_liveTank.clear();
}

void NoteLiveIncoming(const std::string& target, uint64_t amount, const std::string& attacker = std::string(), const std::string& type = std::string("Hit"))
{
    if (target.empty() || amount == 0) return;
    int64_t now = NowMs();
    std::lock_guard<std::mutex> lk(g_liveTankMutex);
    auto& t = g_liveTank[target];
    if (t.firstMs == 0) t.firstMs = now;
    t.damage += amount;
    t.hits += 1;
    if (amount > t.maxHit) t.maxHit = (uint32_t)std::min<uint64_t>(amount, UINT32_MAX);
    t.lastMs = now;

    LiveTankHitEvent ev;
    ev.ms = now;
    ev.amount = (uint32_t)std::min<uint64_t>(amount, UINT32_MAX);
    ev.attacker = attacker.empty() ? std::string("mob") : attacker;
    ev.type = type.empty() ? std::string("Hit") : type;
    t.hitEvents.push_back(ev);
    if (t.hitEvents.size() > 300)
        t.hitEvents.erase(t.hitEvents.begin(), t.hitEvents.begin() + (t.hitEvents.size() - 300));
    t.lastHits.push_back(ev);
    if (t.lastHits.size() > 10)
        t.lastHits.erase(t.lastHits.begin(), t.lastHits.begin() + (t.lastHits.size() - 10));
}

void NoteLiveAvoid(const std::string& target, const std::string& kind)
{
    if (target.empty()) return;
    int64_t now = NowMs();
    std::lock_guard<std::mutex> lk(g_liveTankMutex);
    auto& t = g_liveTank[target];
    if (_stricmp(kind.c_str(), "miss") == 0) ++t.misses;
    else if (_stricmp(kind.c_str(), "dodge") == 0) ++t.dodges;
    else if (_stricmp(kind.c_str(), "parry") == 0) ++t.parries;
    else if (_stricmp(kind.c_str(), "riposte") == 0) ++t.ripostes;
    else if (_stricmp(kind.c_str(), "block") == 0) ++t.blocks;
    t.lastMs = now;
}

// Tank data is live-only in this stage of the plugin UI. If a mob despawns or
// the raid stops taking hits without a slain message, clear the live tank rows
// after the same inactivity timeout as DPS. This prevents the Tank page from
// staying "live" forever after despawn/evac/FD/reset events.
static void HP_MaybeClearTimedOutLiveTank()
{
    const int64_t now = NowMs();
    std::lock_guard<std::mutex> lk(g_liveTankMutex);
    if (g_liveTank.empty()) return;

    int64_t newest = 0;
    uint64_t total = 0;
    for (const auto& kv : g_liveTank) {
        if (kv.second.lastMs > newest) newest = kv.second.lastMs;
        total += kv.second.damage;
        total += HP_TankSwings(kv.second);
    }

    // Keep the tank breakdown visible briefly after DPS archives so the user can
    // click the Tank tab/review the last despawned or timed-out fight.  It still
    // clears automatically, just not at the exact same instant as the DPS fight.
    constexpr int64_t kTankReviewLingerMs = 30000;
    if (newest > 0 && total > 0 && (now - newest) > (kLiveDpsTimeoutMs + kTankReviewLingerMs)) {
        g_liveTank.clear();
        if (g_debug.load())
            WriteChatf("\ag[HealParse]\ax cleared stale live tank data after tank review linger");
    }
}

// ----------------------------------------------------------------------------
// Live BURN / discipline timers. The plugin does not detect burns itself; the
// HealTracker Lua disc/AA listeners push them here with:
//     /healparse burn <who>|<label>|<seconds>
// Each entry counts down and self-expires. Optional third view of the overlay.
// ----------------------------------------------------------------------------
struct LiveBurn {
    std::string who;
    std::string label;
    int64_t     endMs = 0;
    int64_t     durMs = 0;
};

std::vector<LiveBurn> g_liveBurns;
std::mutex g_liveBurnsMutex;

static void HP_RecordLiveDpsSpellCast(const std::string& caster, const std::string& spell);
static void HP_RecordDpsBurnForFight(const std::string& who, const std::string& label)
{
    std::string cleanWho = HP_TrimCopy(who);
    std::string cleanLabel = HP_TrimCopy(label);
    if (cleanWho.empty() || cleanLabel.empty()) return;

    std::string low = LowerCopy(cleanLabel);
    const bool melee = low.find("melee") != std::string::npos
                    || low.find("disc") != std::string::npos
                    || low.find("discipline") != std::string::npos
                    || low.find("frenzy") != std::string::npos
                    || low.find("flurry") != std::string::npos
                    || low.find("rage") != std::string::npos
                    || low.find("blade") != std::string::npos
                    || low.find("palm") != std::string::npos
                    || low.find("burnout") != std::string::npos;

    std::string display = (melee ? "Melee Burn: " : "Burn: ") + cleanLabel;
    HP_RecordLiveDpsSpellCast(cleanWho, display);
}

void AddLiveBurn(const std::string& who, const std::string& label, int seconds)
{
    if (who.empty() || seconds <= 0) return;
    const int64_t now = NowMs();
    std::lock_guard<std::mutex> lk(g_liveBurnsMutex);
    // Refresh an existing same who+label timer instead of stacking duplicates.
    for (auto& b : g_liveBurns) {
        if (b.who == who && b.label == label) {
            b.durMs = (int64_t)seconds * 1000;
            b.endMs = now + b.durMs;
            return;
        }
    }
    if (g_liveBurns.size() > 64) g_liveBurns.clear(); // safety bound
    LiveBurn b; b.who = who; b.label = label;
    b.durMs = (int64_t)seconds * 1000; b.endMs = now + b.durMs;
    g_liveBurns.push_back(std::move(b));

    // Also show caster/melee burns in the DPS Top Spells / View All Spells section,
    // tied only to the active fight. Refreshing an existing timer does not add
    // another cast; a new burn activation does.
    HP_RecordDpsBurnForFight(who, label);
}

std::string BuildLiveDpsSnapshot()
{
    const int64_t now = NowMs();
    std::lock_guard<std::mutex> lk(g_liveDpsMutex);
    if (g_liveDps.mob.empty() || (now - g_liveDps.lastDamageMs) > kLiveDpsTimeoutMs) {
        return std::string("active=0");
    }

    struct RowOut { std::string name; uint64_t total; uint32_t count; uint32_t maxHit; };
    std::vector<RowOut> rows;
    rows.reserve(g_liveDps.players.size());
    for (const auto& kv : g_liveDps.players) {
        if (kv.second.total == 0) continue;
        rows.push_back(RowOut{kv.first, kv.second.total, kv.second.count, kv.second.maxHit});
    }
    std::sort(rows.begin(), rows.end(), [](const RowOut& a, const RowOut& b) {
        return a.total > b.total;
    });
    if (rows.size() > 10) rows.resize(10);

    std::string mob = g_liveDps.mob;
    EscapeEventValue(mob);
    std::string out = "active=1|mob=" + mob;
    out += "|total=" + std::to_string(g_liveDps.total);
    out += "|started=" + std::to_string(g_liveDps.startedMs);
    out += "|now=" + std::to_string(now);
    out += "|rows=";
    bool first = true;
    for (auto& r : rows) {
        std::string name = r.name;
        EscapeEventValue(name);
        if (!first) out += ";";
        first = false;
        out += name;
        out += "," + std::to_string(r.total);
        out += "," + std::to_string(r.count);
        out += "," + std::to_string(r.maxHit);
    }
    return out;
}


std::string HT_FormatShort(uint64_t v)
{
    char b[64] = { 0 };
    if (v >= 1000000ULL) {
        std::snprintf(b, sizeof(b), "%.3fm", (double)v / 1000000.0);
    } else if (v >= 1000ULL) {
        std::snprintf(b, sizeof(b), "%lluk", (unsigned long long)((v + 500ULL) / 1000ULL));
    } else {
        std::snprintf(b, sizeof(b), "%llu", (unsigned long long)v);
    }
    return std::string(b);
}

// Compact one-decimal formatter for live mini total damage/healing values.
// Keeps one decimal for k/m values so the mini never rounds 105.6k down to 106k or 105k.
std::string HT_FormatShort1(uint64_t v)
{
    char b[64] = { 0 };
    if (v >= 1000000ULL) {
        std::snprintf(b, sizeof(b), "%.1fm", (double)v / 1000000.0);
    } else if (v >= 1000ULL) {
        std::snprintf(b, sizeof(b), "%.1fk", (double)v / 1000.0);
    } else {
        std::snprintf(b, sizeof(b), "%llu", (unsigned long long)v);
    }
    return std::string(b);
}

// Compact one-decimal formatter for live mini DPS/HPS rates.
// Always keeps one decimal for k/m rates.
// Examples: 24500 -> 24.5k, 105600 -> 105.6k, 82000 -> 82.0k.

// Live mini top Total formatter. Shows raid total damage in millions with
// exactly 3 decimals and no suffix, e.g. 4,636,000 -> 4.636.
std::string HT_FormatLiveTotalMillions3(uint64_t v)
{
    char b[64] = { 0 };
    if (v >= 1000000ULL)
        std::snprintf(b, sizeof(b), "%.3fm", (double)v / 1000000.0);
    else if (v >= 1000ULL)
        std::snprintf(b, sizeof(b), "%.3fk", (double)v / 1000.0);
    else
        std::snprintf(b, sizeof(b), "%llu", (unsigned long long)v);
    return std::string(b);
}

std::string HT_FormatRateShort1(uint64_t v)
{
    char b[64] = { 0 };
    if (v >= 1000000ULL) {
        std::snprintf(b, sizeof(b), "%.1fm", (double)v / 1000000.0);
    } else if (v >= 1000ULL) {
        std::snprintf(b, sizeof(b), "%.1fk", (double)v / 1000.0);
    } else {
        std::snprintf(b, sizeof(b), "%llu", (unsigned long long)v);
    }
    return std::string(b);
}

std::string HT_FormatInteger(uint64_t v)
{
    char raw[64] = { 0 };
    std::snprintf(raw, sizeof(raw), "%llu", (unsigned long long)v);
    std::string s(raw);
    std::string out;
    int n = 0;
    for (auto it = s.rbegin(); it != s.rend(); ++it) {
        if (n && (n % 3) == 0) out.push_back(',');
        out.push_back(*it);
        ++n;
    }
    std::reverse(out.begin(), out.end());
    return out;
}

// Small vector emblem drawn per view (no icon-font dependency, works on any MQ build).
static void HT_DrawEmblem(ImDrawList* dl, ImVec2 c, float s, int kind, ImU32 col)
{
    if (kind == 1) {            // heals: medical cross
        float t = s * 0.36f;
        dl->AddRectFilled(ImVec2(c.x - t, c.y - s), ImVec2(c.x + t, c.y + s), col, 2.0f);
        dl->AddRectFilled(ImVec2(c.x - s, c.y - t), ImVec2(c.x + s, c.y + t), col, 2.0f);
    } else if (kind == 2) {     // burns: flame
        ImVec2 p1(c.x, c.y - s), p2(c.x + s * 0.92f, c.y + s), p3(c.x - s * 0.92f, c.y + s);
        dl->AddTriangleFilled(p1, p2, p3, col);
        dl->AddCircleFilled(ImVec2(c.x, c.y + s * 0.30f), s * 0.46f, IM_COL32(255, 226, 150, 255));
    } else {                    // dps: crossed blades
        float th = 2.6f;
        dl->AddLine(ImVec2(c.x - s, c.y + s), ImVec2(c.x + s, c.y - s), col, th);
        dl->AddLine(ImVec2(c.x - s, c.y - s), ImVec2(c.x + s, c.y + s), col, th);
        dl->AddCircleFilled(ImVec2(c.x - s, c.y + s), 1.8f, col);
        dl->AddCircleFilled(ImVec2(c.x + s, c.y + s), 1.8f, col);
    }
}

static void HP_DrawGhostIcon(ImDrawList* dl, ImVec2 p, float size);

void DrawHealParseLiveDpsOverlay()
{
    g_liveOverlayFrames.fetch_add(1, std::memory_order_relaxed);
    if (!g_liveOverlayEnabled.load()) return;

    const int64_t now = NowMs();
    int view = g_liveOverlayView.load();
    if (view < 0 || view > 2) view = 0;

    struct Theme { ImU32 accent, bar, bg; const char* title; int icon; };
    static const Theme THEMES[3] = {
        { IM_COL32( 70,170,255,255), IM_COL32( 70,170,255, 48), IM_COL32(  9, 17, 33,255), "DPS Tracker",   0 },
        { IM_COL32( 70,210,120,255), IM_COL32( 70,210,120, 48), IM_COL32(  9, 26, 18,255), "Heals Tracker", 1 },
        { IM_COL32(255,150, 55,255), IM_COL32(255,150, 55, 48), IM_COL32( 28, 18,  9,255), "Burn Timers",   2 },
    };
    const Theme& th = THEMES[view];

    const ImU32 C_TEXT = IM_COL32(236, 239, 245, 255);
    const ImU32 C_MUTE = IM_COL32(150, 160, 176, 255);
    const ImU32 C_RANK = IM_COL32(120, 132, 150, 255);
    const ImU32 C_MOB  = IM_COL32(235,  84,  84, 255);

    struct Row { std::string left; std::string right; double frac; };
    std::vector<Row> rows;
    std::string subtitle;
    std::string sTotL, sTotV, sRateL, sRateV, sTimeV;
    bool active = false;

    char b1[96], b2[96], b3[96];

    if (view == 0) {                                   // ---------- DPS ----------
        std::string mob; uint64_t total = 0; int64_t startedMs = 0;
        struct R { std::string n; uint64_t t; };
        std::vector<R> rr;
        {
            std::lock_guard<std::mutex> lk(g_liveDpsMutex);
            active = (!g_liveDps.mob.empty() && (now - g_liveDps.lastDamageMs) <= kLiveDpsTimeoutMs);
            if (active) {
                mob = g_liveDps.mob; total = g_liveDps.total; startedMs = g_liveDps.startedMs;
                std::unordered_map<std::string, uint64_t> acc;
                for (auto& kv : g_liveDps.players) {
                    if (!kv.second.total) continue;
                    std::string rowName = HP_GetPetCombinedDisplayName(kv.first);
                    if (HP_ShouldHideDpsDisplayRow(rowName, mob)) continue;
                    acc[rowName] += kv.second.total;
                }
                rr.reserve(acc.size());
                for (auto& akv : acc) rr.push_back({ akv.first, akv.second });
            }
        }
        if (active) {
            uint64_t displayTotal = 0;
            for (const auto& r : rr) displayTotal += r.t;
            if (displayTotal > 0) total = displayTotal;
        }
        int dur = active ? (int)std::max<int64_t>(1, (now - startedMs) / 1000) : 0;
        std::sort(rr.begin(), rr.end(), [](const R& a, const R& b) { return a.t > b.t; });
        if (rr.size() > 10) rr.resize(10);
        uint64_t topv = rr.empty() ? 1 : rr.front().t;
        subtitle = active ? mob : "Waiting for combat";
        // Top live DPS total: show millions with 3 decimals and no suffix (example: 4.636).
        // Player rows still use the compact one-decimal k/m formatter.
        sTotL = "Total"; sTotV = HT_FormatLiveTotalMillions3(total);
        sRateL = "DPS";  sRateV = HT_FormatInteger(active ? total / (uint64_t)std::max(1, dur) : 0);
        snprintf(b3, sizeof(b3), "%02d:%02d", dur / 60, dur % 60); sTimeV = b3;
        int i = 0;
        for (auto& r : rr) {
            uint64_t dps = r.t / (uint64_t)std::max(1, dur);
            double pct = total > 0 ? (double)r.t * 100.0 / (double)total : 0.0;
            snprintf(b1, sizeof(b1), "%d. %s", ++i, r.n.c_str());
            snprintf(b2, sizeof(b2), "%s @ %s  %.0f%%", HT_FormatShort1(r.t).c_str(), HT_FormatInteger(dps).c_str(), pct);
            rows.push_back({ b1, b2, topv > 0 ? (double)r.t / (double)topv : 0.0 });
        }
    } else if (view == 1) {                            // ---------- HEALS ----------
        uint64_t total = 0; int64_t startedMs = 0;
        struct R { std::string n; uint64_t t; };
        std::vector<R> rr;
        {
            std::lock_guard<std::mutex> lk(g_liveHealsMutex);
            active = (g_liveHeals.startedMs != 0 && (now - g_liveHeals.lastHealMs) <= kLiveDpsTimeoutMs && g_liveHeals.total > 0);
            if (active) {
                total = g_liveHeals.total; startedMs = g_liveHeals.startedMs;
                rr.reserve(g_liveHeals.healers.size());
                for (auto& kv : g_liveHeals.healers) if (kv.second.total) rr.push_back({ kv.first, kv.second.total });
            }
        }
        int dur = active ? (int)std::max<int64_t>(1, (now - startedMs) / 1000) : 0;
        std::sort(rr.begin(), rr.end(), [](const R& a, const R& b) { return a.t > b.t; });
        if (rr.size() > 10) rr.resize(10);
        uint64_t topv = rr.empty() ? 1 : rr.front().t;
        subtitle = active ? "Raid healing" : "Waiting for heals";
        sTotL = "Total"; sTotV = HT_FormatShort1(total);
        sRateL = "HPS";  sRateV = HT_FormatInteger(active ? total / (uint64_t)std::max(1, dur) : 0);
        snprintf(b3, sizeof(b3), "%02d:%02d", dur / 60, dur % 60); sTimeV = b3;
        int i = 0;
        for (auto& r : rr) {
            uint64_t hps = r.t / (uint64_t)std::max(1, dur);
            double pct = total > 0 ? (double)r.t * 100.0 / (double)total : 0.0;
            snprintf(b1, sizeof(b1), "%d. %s", ++i, r.n.c_str());
            snprintf(b2, sizeof(b2), "%s @ %s  %.0f%%", HT_FormatShort1(r.t).c_str(), HT_FormatRateShort1(hps).c_str(), pct);
            rows.push_back({ b1, b2, topv > 0 ? (double)r.t / (double)topv : 0.0 });
        }
    } else {                                           // ---------- BURNS ----------
        struct B { std::string who, label; int64_t rem, dur; };
        std::vector<B> bb;
        {
            std::lock_guard<std::mutex> lk(g_liveBurnsMutex);
            g_liveBurns.erase(std::remove_if(g_liveBurns.begin(), g_liveBurns.end(),
                [&](const LiveBurn& x) { return x.endMs <= now; }), g_liveBurns.end());
            for (auto& x : g_liveBurns) bb.push_back({ x.who, x.label, x.endMs - now, x.durMs });
        }
        active = !bb.empty();
        std::sort(bb.begin(), bb.end(), [](const B& a, const B& b) {
            // Burn mini ordering: group alphabetically by player name first,
            // then show that player's shortest remaining timer above longer ones.
            std::string aw = LowerCopy(HP_TrimCopy(a.who));
            std::string bw = LowerCopy(HP_TrimCopy(b.who));
            if (aw != bw) return aw < bw;
            if (a.rem != b.rem) return a.rem < b.rem;
            return LowerCopy(HP_TrimCopy(a.label)) < LowerCopy(HP_TrimCopy(b.label));
        });
        if (bb.size() > 10) bb.resize(10);
        subtitle = active ? "Active burns" : "No active burns";
        snprintf(b3, sizeof(b3), "%d", (int)bb.size());
        sTotL = "Active"; sTotV = b3; sRateL = ""; sRateV = ""; sTimeV = "";
        for (auto& x : bb) {
            int rs = (int)(x.rem / 1000); if (rs < 0) rs = 0;
            snprintf(b1, sizeof(b1), "%s - %s", x.who.empty() ? "Unknown" : x.who.c_str(), x.label.c_str());
            snprintf(b2, sizeof(b2), "%d:%02d", rs / 60, rs % 60);
            rows.push_back({ b1, b2, x.dur > 0 ? (double)x.rem / (double)x.dur : 0.0 });
        }
    }

    if (!active && !g_liveOverlayForceVisible.load()) return;

    const float PANEL_W = 340.0f;
    const float PAD = 12.0f;
    const float innerW = PANEL_W - PAD * 2.0f;

    int alphaPct = g_liveOverlayAlphaPercent.load();
    if (alphaPct < 15) alphaPct = 15;
    if (alphaPct > 100) alphaPct = 100;

    ImGui::SetNextWindowBgAlpha((float)alphaPct / 100.0f);
    ImGui::SetNextWindowSizeConstraints(ImVec2(PANEL_W, 0.0f), ImVec2(PANEL_W, 100000.0f));
    if (g_liveOverlayResetPos.exchange(false))
        ImGui::SetNextWindowPos(ImVec2(560.0f, 220.0f), ImGuiCond_Always);
    else
        ImGui::SetNextWindowPos(ImVec2(560.0f, 220.0f), ImGuiCond_FirstUseEver);

    ImGui::PushStyleVar(ImGuiStyleVar_WindowRounding, 11.0f);
    ImGui::PushStyleVar(ImGuiStyleVar_WindowBorderSize, 1.5f);
    ImGui::PushStyleVar(ImGuiStyleVar_WindowPadding, ImVec2(PAD, PAD));
    ImGui::PushStyleColor(ImGuiCol_WindowBg, th.bg);
    ImGui::PushStyleColor(ImGuiCol_Border, th.accent);

    ImGuiWindowFlags flags = ImGuiWindowFlags_AlwaysAutoResize
        | ImGuiWindowFlags_NoResize | ImGuiWindowFlags_NoTitleBar
        | ImGuiWindowFlags_NoCollapse | ImGuiWindowFlags_NoFocusOnAppearing
        | ImGuiWindowFlags_NoNav | ImGuiWindowFlags_NoScrollbar;

    bool open = true;
    if (HP_ApplyGlobalScrollbarStyle();

ImGui::Begin("###HealParsePluginLiveDPS", &open, flags)) {
        ImDrawList* dl = ImGui::GetWindowDrawList();
        ImVec2 p0 = ImGui::GetCursorScreenPos();
        const float lineH = ImGui::GetTextLineHeight();
        const ImU32 accLow = (th.accent & 0x00FFFFFFu) | 0x33000000u;

        // ---- header ----
        const float headH = 30.0f;
        dl->AddRectFilledMultiColor(
            ImVec2(p0.x - 2, p0.y - 2), ImVec2(p0.x + innerW + 2, p0.y + headH - 6),
            accLow, 0x00000000u, 0x00000000u, accLow);
        // Mini tracker top-left icon: use DPS.png for the DPS view instead of the drawn X swords.
        // DPS.png is loaded from the same Images folder as the other HealTracker PNGs.
        if (view == 0) {
            HP_LoadDpsIconTextureIfNeeded();
            if (g_dpsIconTexture.id)
                HP_DrawImageIcon(dl, g_dpsIconTexture, ImVec2(p0.x + 0.0f, p0.y - 2.0f), 24.0f);
            else
                HT_DrawEmblem(dl, ImVec2(p0.x + 10, p0.y + 9), 8.0f, th.icon, th.accent);
        } else {
            HT_DrawEmblem(dl, ImVec2(p0.x + 10, p0.y + 9), 8.0f, th.icon, th.accent);
        }
        dl->AddText(ImVec2(p0.x + 28, p0.y + 1), th.accent, th.title);

        // Header controls: small rounded buttons with clear text labels.
        // Keep them left of the view dots so nothing overlaps.
        float btnY = p0.y - 1.0f;
        float cycleX = p0.x + innerW - 126.0f;
        float uiX    = p0.x + innerW - 92.0f;
        ImGui::PushStyleVar(ImGuiStyleVar_FrameRounding, 14.0f);
        ImGui::PushStyleVar(ImGuiStyleVar_FramePadding, ImVec2(0.0f, 0.0f));
        ImGui::PushStyleColor(ImGuiCol_Button,        IM_COL32(18, 42, 78, 235));
        ImGui::PushStyleColor(ImGuiCol_ButtonHovered, IM_COL32(36, 95, 170, 250));
        ImGui::PushStyleColor(ImGuiCol_ButtonActive,  IM_COL32(50, 130, 220, 255));
        ImGui::PushStyleColor(ImGuiCol_Text,          IM_COL32(230, 245, 255, 255));

        ImGui::SetCursorScreenPos(ImVec2(cycleX, btnY));
        // Refresh/cycle button for mini DPS window. Uses Cycle.png if present
        // in the same Images folder as the other HealTracker PNGs.
        HP_LoadRefreshIconTextureIfNeeded();
        if (ImGui::Button("##ht_header_cycle_refresh_icon", ImVec2(26.0f, 24.0f)))
            g_liveOverlayView.store((view + 1) % 3);
        {
            ImVec2 ca = ImGui::GetItemRectMin();
            if (g_refreshIconTexture.id) {
                HP_DrawImageIcon(ImGui::GetWindowDrawList(), g_refreshIconTexture, ImVec2(ca.x + 4.0f, ca.y + 3.0f), 18.0f);
            } else {
                ImGui::GetWindowDrawList()->AddText(ImVec2(ca.x + 6.0f, ca.y + 2.0f), IM_COL32(230, 245, 255, 255), u8"↻");
            }
        }
        if (ImGui::IsItemHovered()) ImGui::SetTooltip("Cycle DPS / Heals / Burns");

        ImGui::SetCursorScreenPos(ImVec2(uiX, btnY));
        // Drawn fallback ghost is used here; no PNG load needed.
        ImGui::PushStyleColor(ImGuiCol_Button,        IM_COL32(105, 62, 205, 255));
        ImGui::PushStyleColor(ImGuiCol_ButtonHovered, IM_COL32(135, 82, 235, 255));
        ImGui::PushStyleColor(ImGuiCol_ButtonActive,  IM_COL32(88, 48, 180, 255));
        if (ImGui::Button("##ht_header_openui_ghost", ImVec2(38.0f, 24.0f))) {
            g_fullUiEnabled.store(true);
            g_fullUiResetPos.store(false);
        }
        ImGui::PopStyleColor(3);
        {
            ImVec2 ga = ImGui::GetItemRectMin();
            HP_DrawGhostIcon(ImGui::GetWindowDrawList(), ImVec2(ga.x + 8.0f, ga.y + 2.0f), 20.0f);
        }
        if (ImGui::IsItemHovered()) ImGui::SetTooltip("Open full HealTracker UI");

        ImGui::PopStyleColor(4);
        ImGui::PopStyleVar(2);

        // View dots and alpha control live on the far right. Keep the view dots
        // far enough left that they do not overlap the alpha circle.
        float alphaX = p0.x + innerW - 10.0f;
        float dotX = p0.x + innerW - 48.0f;
        float dotY = p0.y + 8.0f;
        for (int d = 0; d < 3; ++d) {
            ImVec2 dc(dotX + d * 10.0f, dotY);
            if (d == view) dl->AddCircleFilled(dc, 3.3f, th.accent);
            else           dl->AddCircle(dc, 2.9f, IM_COL32(120, 130, 145, 255), 0, 1.3f);
        }

        ImVec2 gc(alphaX, p0.y + 8.0f);
        dl->AddCircle(gc, 5.6f, C_MUTE, 0, 1.5f);
        dl->AddCircleFilled(gc, 1.8f, C_MUTE);
        dl->AddLine(ImVec2(p0.x - 2, p0.y + headH - 6), ImVec2(p0.x + innerW + 2, p0.y + headH - 6),
            (th.accent & 0x00FFFFFFu) | 0x66000000u, 1.4f);

        ImGui::SetCursorScreenPos(p0);
        if (ImGui::InvisibleButton("##ht_title", ImVec2(innerW - 160.0f, headH - 6.0f))) {
            g_fullUiEnabled.store(true);
            g_fullUiResetPos.store(false);
        }
        ImGui::SetCursorScreenPos(ImVec2(dotX - 6.0f, p0.y));
        if (ImGui::InvisibleButton("##ht_cycle_dots", ImVec2(38.0f, headH - 6.0f)))
            g_liveOverlayView.store((view + 1) % 3);
        if (ImGui::IsItemHovered()) ImGui::SetTooltip("Cycle DPS / Heals / Burns");

        ImGui::SetCursorScreenPos(ImVec2(gc.x - 8.0f, p0.y));
        if (ImGui::InvisibleButton("##ht_alpha_circle", ImVec2(18.0f, headH - 6.0f))) {
            int a = g_liveOverlayAlphaPercent.load();
            a = (a >= 100) ? 80 : (a >= 80 ? 60 : 100);
            g_liveOverlayAlphaPercent.store(a);
        }
        if (ImGui::IsItemHovered()) {
            ImGui::SetTooltip("Overlay/Main UI alpha: %d%%\nClick to cycle 100%% / 80%% / 60%%", g_liveOverlayAlphaPercent.load());
        }
        ImGui::SetCursorScreenPos(ImVec2(p0.x, p0.y + headH));

        // ---- subtitle ----
        {
            ImU32 subCol = !active ? C_MUTE : (view == 2 ? th.accent : C_MOB);
            ImVec2 sp = ImGui::GetCursorScreenPos();
            dl->AddText(sp, subCol, subtitle.c_str());
            ImGui::Dummy(ImVec2(innerW, lineH + 3.0f));
        }

        // ---- stats line ----
        {
            ImVec2 sp = ImGui::GetCursorScreenPos();
            float x = sp.x;
            auto seg = [&](const std::string& lbl, const std::string& val, ImU32 lblC) {
                if (lbl.empty() && val.empty()) return;
                if (!lbl.empty()) {
                    std::string l = lbl + ":";
                    dl->AddText(ImVec2(x, sp.y), lblC, l.c_str());
                    x += ImGui::CalcTextSize(l.c_str()).x + 4.0f;
                }
                if (!val.empty()) {
                    dl->AddText(ImVec2(x, sp.y), C_TEXT, val.c_str());
                    x += ImGui::CalcTextSize(val.c_str()).x + 12.0f;
                }
            };
            seg(sTotL, sTotV, C_MUTE);
            seg(sRateL, sRateV, th.accent);
            if (!sTimeV.empty()) seg("Time", sTimeV, C_MUTE);
            ImGui::Dummy(ImVec2(innerW, lineH + 4.0f));
        }

        // ---- separator ----
        {
            ImVec2 sp = ImGui::GetCursorScreenPos();
            dl->AddLine(ImVec2(sp.x, sp.y + 1), ImVec2(sp.x + innerW, sp.y + 1), IM_COL32(255, 255, 255, 28), 1.0f);
            ImGui::Dummy(ImVec2(innerW, 5.0f));
        }

        // ---- rows ----
        const float rowH = lineH + 6.0f;
        if (rows.empty()) {
            ImVec2 sp = ImGui::GetCursorScreenPos();
            const char* msg = (view == 2) ? "No active burns" : "No data yet";
            ImVec2 ts = ImGui::CalcTextSize(msg);
            dl->AddText(ImVec2(sp.x + (innerW - ts.x) * 0.5f, sp.y + 4), C_MUTE, msg);
            ImGui::Dummy(ImVec2(innerW, rowH + 4.0f));
        }
        for (auto& r : rows) {
            ImVec2 sp = ImGui::GetCursorScreenPos();
            double frac = r.frac; if (frac < 0) frac = 0; if (frac > 1) frac = 1;
            float bw = (float)(innerW * frac);
            if (bw > 2.0f)
                dl->AddRectFilled(ImVec2(sp.x, sp.y + 1.0f), ImVec2(sp.x + bw, sp.y + rowH - 1.0f), th.bar, 3.0f);
            const char* lt = r.left.c_str();
            const char* dotp = strchr(lt, '.');
            if (dotp && *(dotp + 1) == ' ') {
                std::string rank(lt, dotp - lt + 1);
                dl->AddText(ImVec2(sp.x + 4, sp.y + 3), C_RANK, rank.c_str());
                float rw = ImGui::CalcTextSize(rank.c_str()).x;
                dl->AddText(ImVec2(sp.x + 8 + rw, sp.y + 3), C_TEXT, dotp + 2);
            } else {
                dl->AddText(ImVec2(sp.x + 4, sp.y + 3), C_TEXT, lt);
            }
            ImVec2 rs = ImGui::CalcTextSize(r.right.c_str());
            dl->AddText(ImVec2(sp.x + innerW - rs.x - 2, sp.y + 3),
                (view == 2) ? th.accent : C_TEXT, r.right.c_str());
            ImGui::Dummy(ImVec2(innerW, rowH));
        }

        // ---- footer divider only (controls live in the header now) ----
        {
            ImVec2 sp = ImGui::GetCursorScreenPos();
            dl->AddLine(ImVec2(sp.x, sp.y + 2), ImVec2(sp.x + innerW, sp.y + 2), IM_COL32(255, 255, 255, 20), 1.0f);
            ImGui::Dummy(ImVec2(innerW, 7.0f));
        }

        // inner rim-light for depth
        ImVec2 wmin = ImGui::GetWindowPos();
        ImVec2 wmax = ImVec2(wmin.x + ImGui::GetWindowWidth(), wmin.y + ImGui::GetWindowHeight());
        dl->AddRect(ImVec2(wmin.x + 2, wmin.y + 2), ImVec2(wmax.x - 2, wmax.y - 2),
            (th.accent & 0x00FFFFFFu) | 0x33000000u, 9.0f, 0, 1.0f);
    }
    ImGui::End();

    ImGui::PopStyleColor(2);
    ImGui::PopStyleVar(3);

    if (!open) g_liveOverlayEnabled.store(false);
}


static void HP_DrawGlowPanel(ImDrawList* dl, ImVec2 a, ImVec2 b, ImU32 col, float round = 10.0f);

static void DrawHealParseAfterFightPopup()
{
    if (!g_afterFightPopupOpen.load()) return;

    CompletedDpsFight f;
    {
        std::lock_guard<std::mutex> lk(g_afterFightPopupMutex);
        f = g_afterFightPopup;
    }
    if (f.mob.empty() || f.total == 0 || f.players.empty()) {
        g_afterFightPopupOpen.store(false);
        return;
    }

    const int linger = std::max(3, g_afterFightPopupLingerSec.load());
    const int64_t now = NowMs();
    if (now - g_afterFightPopupShownMs.load() > (int64_t)linger * 1000) {
        g_afterFightPopupOpen.store(false);
        return;
    }

    struct Row { std::string name; uint64_t dmg = 0; uint32_t maxHit = 0; uint32_t hits = 0; };
    std::vector<Row> rows;
    std::unordered_map<std::string, Row> acc;
    for (const auto& kv : f.players) {
        if (kv.second.total == 0) continue;
        std::string rowName = HP_GetPetCombinedDisplayName(kv.first);
        if (HP_ShouldHideDpsDisplayRow(rowName, f.mob)) continue;
        auto& r = acc[rowName];
        r.name = rowName;
        r.dmg += kv.second.total;
        r.hits += kv.second.count;
        if (kv.second.maxHit > r.maxHit) r.maxHit = kv.second.maxHit;
    }
    rows.reserve(acc.size());
    uint64_t displayTotal = 0;
    for (auto& akv : acc) { rows.push_back(akv.second); displayTotal += akv.second.dmg; }
    if (displayTotal == 0) displayTotal = f.total;
    std::sort(rows.begin(), rows.end(), [](const Row& a, const Row& b) { return a.dmg > b.dmg; });
    if (rows.size() > 10) rows.resize(10);

    const int dur = (int)std::max<int64_t>(1, (f.endedMs - f.startedMs) / 1000);
    const uint64_t raidDps = displayTotal / (uint64_t)std::max(1, dur);

    float longestName = 0.0f;
    float longestValue = 0.0f;
    for (size_t i = 0; i < rows.size(); ++i) {
        char left[256];
        std::snprintf(left, sizeof(left), "%d. %s", (int)i + 1, rows[i].name.c_str());
        longestName = std::max(longestName, ImGui::CalcTextSize(left).x);
        uint64_t dps = rows[i].dmg / (uint64_t)std::max(1, dur);
        double pct = displayTotal > 0 ? (double)rows[i].dmg * 100.0 / (double)displayTotal : 0.0;
        char right[192];
        std::snprintf(right, sizeof(right), "%s @ %s [%.0f%%]", HT_FormatShort1(rows[i].dmg).c_str(), HT_FormatInteger(dps).c_str(), pct);
        longestValue = std::max(longestValue, ImGui::CalcTextSize(right).x);
    }

    const float pad = 12.0f;
    const float minW = 390.0f;
    const float desiredW = std::min(720.0f, std::max(minW, longestName + longestValue + 64.0f));
    const float innerW = desiredW - pad * 2.0f;
    const float rowH = ImGui::GetTextLineHeight() + 7.0f;
    const float desiredH = 150.0f + (float)rows.size() * rowH;

    ImGui::SetNextWindowSize(ImVec2(desiredW, desiredH), ImGuiCond_Always);
    ImGui::SetNextWindowPos(ImVec2(520.0f, 260.0f), ImGuiCond_FirstUseEver);
    ImGui::SetNextWindowBgAlpha((float)std::max(15, std::min(100, g_liveOverlayAlphaPercent.load())) / 100.0f);

    ImGui::PushStyleVar(ImGuiStyleVar_WindowRounding, 15.0f);
    ImGui::PushStyleVar(ImGuiStyleVar_WindowBorderSize, 1.6f);
    ImGui::PushStyleVar(ImGuiStyleVar_WindowPadding, ImVec2(pad, pad));
    ImGui::PushStyleColor(ImGuiCol_WindowBg, IM_COL32(4, 8, 18, 242));
    ImGui::PushStyleColor(ImGuiCol_Border, IM_COL32(80, 190, 255, 190));

    bool open = true;
    ImGuiWindowFlags flags = ImGuiWindowFlags_NoCollapse | ImGuiWindowFlags_NoResize | ImGuiWindowFlags_AlwaysAutoResize | ImGuiWindowFlags_NoScrollbar | ImGuiWindowFlags_NoScrollWithMouse;
    if (ImGui::Begin("Last Fight Summary###HealParseAfterFightPopup", &open, flags)) {
        ImDrawList* dl = ImGui::GetWindowDrawList();
        ImVec2 wp = ImGui::GetWindowPos();
        ImVec2 ws = ImGui::GetWindowSize();

        // Safety guard: if ImGui restores a bad position with the title bar off-screen,
        // pull the main UI back to a draggable visible spot instead of leaving it stuck.
        if (wp.y < 20.0f || wp.x < -ws.x + 160.0f) {
            ImVec2 safePos = HP_GetCenteredFullUiPos();
            ImGui::SetWindowPos(safePos, ImGuiCond_Always);
            wp = safePos;
        }
        HP_DrawGlowPanel(dl, ImVec2(wp.x+4, wp.y+4), ImVec2(wp.x+ws.x-4, wp.y+ws.y-4), IM_COL32(80, 190, 255, 145), 14.0f);

        ImVec2 p0 = ImGui::GetCursorScreenPos();
        ImGui::SetCursorScreenPos(ImVec2(p0.x, p0.y + 2));
        ImGui::TextColored(ImVec4(1.0f, 0.88f, 0.18f, 1.0f), "Last Fight Summary");
        ImGui::SetCursorScreenPos(ImVec2(p0.x, p0.y + 30.0f));

        ImGui::Separator();
        ImGui::TextColored(ImVec4(1.0f, 0.28f, 0.28f, 1.0f), "%s", f.mob.c_str());
        ImGui::SameLine();
        ImGui::TextColored(ImVec4(1.0f, 0.84f, 0.12f, 1.0f), "%s @ %s in %ds", HT_FormatShort1(displayTotal).c_str(), HT_FormatInteger(raidDps).c_str(), dur);
        ImGui::Separator();

        const uint64_t topv = rows.empty() ? 1 : rows.front().dmg;
        for (size_t i = 0; i < rows.size(); ++i) {
            const Row& r = rows[i];
            uint64_t dps = r.dmg / (uint64_t)std::max(1, dur);
            double pct = displayTotal > 0 ? (double)r.dmg * 100.0 / (double)displayTotal : 0.0;
            double frac = topv > 0 ? (double)r.dmg / (double)topv : 0.0;
            if (frac < 0.0) frac = 0.0; if (frac > 1.0) frac = 1.0;

            ImVec2 rp = ImGui::GetCursorScreenPos();
            ImU32 rowBg = (i % 2 == 0) ? IM_COL32(13, 57, 112, 210) : IM_COL32(7, 34, 74, 210);
            dl->AddRectFilled(ImVec2(rp.x, rp.y), ImVec2(rp.x + innerW, rp.y + rowH), rowBg, 4.0f);
            dl->AddRectFilled(ImVec2(rp.x, rp.y), ImVec2(rp.x + (float)(innerW * frac), rp.y + rowH), IM_COL32(35, 90, 210, 85), 4.0f);

            char left[256];
            std::snprintf(left, sizeof(left), "%d. %s", (int)i + 1, r.name.c_str());
            dl->AddText(ImVec2(rp.x + 6.0f, rp.y + 3.0f), IM_COL32(255, 230, 40, 255), left);

            char right[192];
            std::snprintf(right, sizeof(right), "%s @ %s [%.0f%%]", HT_FormatShort1(r.dmg).c_str(), HT_FormatInteger(dps).c_str(), pct);
            ImVec2 rs = ImGui::CalcTextSize(right);
            dl->AddText(ImVec2(rp.x + innerW - rs.x - 6.0f, rp.y + 3.0f), IM_COL32(255, 230, 40, 255), right);
            ImGui::Dummy(ImVec2(innerW, rowH));
        }

        // Extra bottom breathing room so the 10th DPS row is never clipped.
        ImGui::Dummy(ImVec2(innerW, 10.0f));
    }
    ImGui::End();

    ImGui::PopStyleColor(2);
    ImGui::PopStyleVar(3);

    if (!open) g_afterFightPopupOpen.store(false);
}

void DrawHealParseAfterFightPopupOncePerFrame()
{
    static int lastFrame = -1;
    int frame = ImGui::GetFrameCount();
    if (frame == lastFrame) return;
    lastFrame = frame;
    DrawHealParseAfterFightPopup();
}



static void HP_SetFullUiTheme()
{
    ImGui::PushStyleVar(ImGuiStyleVar_WindowRounding, 13.0f);
    ImGui::PushStyleVar(ImGuiStyleVar_ChildRounding, 10.0f);
    ImGui::PushStyleVar(ImGuiStyleVar_FrameRounding, 6.0f);
    ImGui::PushStyleVar(ImGuiStyleVar_WindowPadding, ImVec2(12.0f, 12.0f));
    ImGui::PushStyleVar(ImGuiStyleVar_ItemSpacing, ImVec2(8.0f, 6.0f));
    // Match every scrollbar in the full UI to the larger, easier-to-grab
    // View All Fight Summary scrollbar style.
    ImGui::PushStyleVar(ImGuiStyleVar_ScrollbarSize, 18.0f);
    ImGui::PushStyleVar(ImGuiStyleVar_ScrollbarRounding, 18.0f);
    ImGui::PushStyleColor(ImGuiCol_WindowBg, IM_COL32(4, 8, 18, 242));
    ImGui::PushStyleColor(ImGuiCol_ChildBg, IM_COL32(7, 13, 28, 218));
    ImGui::PushStyleColor(ImGuiCol_Border, IM_COL32(60, 145, 255, 150));
    ImGui::PushStyleColor(ImGuiCol_FrameBg, IM_COL32(12, 22, 42, 230));
    ImGui::PushStyleColor(ImGuiCol_FrameBgHovered, IM_COL32(22, 55, 95, 235));
    ImGui::PushStyleColor(ImGuiCol_Button, IM_COL32(18, 38, 72, 230));
    ImGui::PushStyleColor(ImGuiCol_ButtonHovered, IM_COL32(30, 88, 150, 245));
    ImGui::PushStyleColor(ImGuiCol_ButtonActive, IM_COL32(50, 132, 225, 255));
    ImGui::PushStyleColor(ImGuiCol_ScrollbarBg, IM_COL32(10, 8, 24, 120));
    ImGui::PushStyleColor(ImGuiCol_ScrollbarGrab, IM_COL32(150, 80, 255, 230));
    ImGui::PushStyleColor(ImGuiCol_ScrollbarGrabHovered, IM_COL32(185, 110, 255, 245));
    ImGui::PushStyleColor(ImGuiCol_ScrollbarGrabActive, IM_COL32(215, 150, 255, 255));
}

static void HP_PopFullUiTheme()
{
    ImGui::PopStyleColor(12);
    ImGui::PopStyleVar(7);
}

static void HP_DrawGlowPanel(ImDrawList* dl, ImVec2 a, ImVec2 b, ImU32 col, float round)
{
    dl->AddRectFilled(a, b, IM_COL32(5, 10, 22, 210), round);
    dl->AddRect(a, b, col, round, 0, 1.2f);
    dl->AddRect(ImVec2(a.x + 2, a.y + 2), ImVec2(b.x - 2, b.y - 2), (col & 0x00FFFFFFu) | 0x33000000u, round - 2.0f, 0, 1.0f);
}

static bool HP_TabButton(const char* label, int tab, ImU32 accent, HP_IconTexture* icon = nullptr)
{
    bool active = (g_fullUiTab.load() == tab);
    if (active) {
        ImGui::PushStyleColor(ImGuiCol_Button, accent);
        ImGui::PushStyleColor(ImGuiCol_ButtonHovered, accent);
        ImGui::PushStyleColor(ImGuiCol_ButtonActive, accent);
    }

    const bool hasIcon = icon && icon->id;
    std::string labelWithIcon;
    // More leading space so the larger PNG icons do not overlap the tab text.
    if (hasIcon) labelWithIcon = std::string("              ") + label;
    const char* buttonLabel = hasIcon ? labelWithIcon.c_str() : label;
    bool clicked = ImGui::Button(buttonLabel, ImVec2(150.0f, 48.0f));
    if (hasIcon) {
        ImVec2 a = ImGui::GetItemRectMin();
        // Larger tab PNGs for each top tab image.
        HP_DrawImageIcon(ImGui::GetWindowDrawList(), *icon, ImVec2(a.x + 8.0f, a.y + 1.0f), 46.0f);
    }

    if (active) ImGui::PopStyleColor(3);
    if (clicked) g_fullUiTab.store(tab);
    return clicked;
}

static bool HP_ToggleSwitch(const char* id, bool* value)
{
    const float w = 44.0f, h = 22.0f;
    ImVec2 p = ImGui::GetCursorScreenPos();
    bool clicked = ImGui::InvisibleButton(id, ImVec2(w, h));
    if (clicked && value) *value = !*value;
    bool on = value && *value;
    ImDrawList* dl = ImGui::GetWindowDrawList();
    ImU32 bg = on ? IM_COL32(52, 165, 78, 255) : IM_COL32(48, 55, 72, 255);
    dl->AddRectFilled(p, ImVec2(p.x + w, p.y + h), bg, h * 0.5f);
    dl->AddRect(p, ImVec2(p.x + w, p.y + h), IM_COL32(115, 140, 180, 130), h * 0.5f, 0, 1.0f);
    float knobX = on ? (p.x + w - h + 2.0f) : (p.x + 2.0f);
    dl->AddCircleFilled(ImVec2(knobX + h * 0.5f - 2.0f, p.y + h * 0.5f), h * 0.38f, IM_COL32(235, 245, 255, 255), 18);
    return clicked;
}

static void HP_DrawGhostIcon(ImDrawList* dl, ImVec2 p, float size)
{
    if (!dl) return;
    ImU32 fill = IM_COL32(235, 230, 255, 255);
    ImU32 eye = IM_COL32(70, 45, 120, 255);
    float r = size * 0.38f;
    ImVec2 c(p.x + size * 0.5f, p.y + size * 0.40f);
    dl->AddCircleFilled(c, r, fill, 24);
    dl->AddRectFilled(ImVec2(c.x - r, c.y), ImVec2(c.x + r, p.y + size * 0.82f), fill, 4.0f);
    float y = p.y + size * 0.82f;
    dl->AddTriangleFilled(ImVec2(c.x - r, y), ImVec2(c.x - r * 0.55f, y), ImVec2(c.x - r * 0.78f, y + size * 0.16f), fill);
    dl->AddTriangleFilled(ImVec2(c.x - r * 0.25f, y), ImVec2(c.x + r * 0.25f, y), ImVec2(c.x, y + size * 0.16f), fill);
    dl->AddTriangleFilled(ImVec2(c.x + r * 0.55f, y), ImVec2(c.x + r, y), ImVec2(c.x + r * 0.78f, y + size * 0.16f), fill);
    dl->AddCircleFilled(ImVec2(c.x - r * 0.32f, c.y - r * 0.08f), size * 0.055f, eye, 10);
    dl->AddCircleFilled(ImVec2(c.x + r * 0.32f, c.y - r * 0.08f), size * 0.055f, eye, 10);
}

static bool HP_MiniGhostButton()
{
    ImGui::PushStyleColor(ImGuiCol_Button, IM_COL32(105, 62, 205, 255));
    ImGui::PushStyleColor(ImGuiCol_ButtonHovered, IM_COL32(135, 82, 235, 255));
    ImGui::PushStyleColor(ImGuiCol_ButtonActive, IM_COL32(88, 48, 180, 255));
    bool clicked = ImGui::Button("          MINI###top_mini_ghost", ImVec2(150.0f, 48.0f));
    ImVec2 a = ImGui::GetItemRectMin();
    HP_DrawGhostIcon(ImGui::GetWindowDrawList(), ImVec2(a.x + 10.0f, a.y + 5.0f), 38.0f);
    ImGui::PopStyleColor(3);
    return clicked;
}

static void HP_StatCard(const char* label, const std::string& value, ImU32 accent, float w = 120.0f)
{
    ImGui::BeginChild(label, ImVec2(w, 62), true, ImGuiWindowFlags_NoScrollbar);
    ImGui::PushStyleColor(ImGuiCol_Text, accent);
    ImGui::TextUnformatted(value.c_str());
    ImGui::PopStyleColor();
    ImGui::TextDisabled("%s", label);
    ImGui::EndChild();
}

struct HP_DpsUiRow {
    std::string name;
    uint64_t dmg = 0;
    uint64_t melee = 0;
    uint64_t spell = 0;
    uint64_t dot = 0;
    uint64_t proc = 0;
    uint64_t pet = 0;
    uint64_t swarm = 0;
    uint64_t other = 0;
    uint32_t hits = 0;
    uint32_t maxHit = 0;
    int64_t maxHitWall = 0;
};
static void HP_AddRowToDpsAccumulator(std::unordered_map<std::string, HP_DpsUiRow>& acc, const std::string& name, const LiveDpsRow& v, bool sourceWasCombinedPet = false)
{
    auto& r = acc[name];
    r.name = name;
    r.dmg += v.total;

    // When Combine Pets is enabled, pet rows are merged into the owner's row.
    // Their original hit type may be melee/spell, but for the DPS type graph and
    // the player's stacked type bar they should still show as Pet damage.
    // Otherwise the main graph can look like no pets contributed at all.
    if (sourceWasCombinedPet) {
        r.pet += v.total;
    } else {
        r.melee += v.melee;
        r.spell += v.spell;
        r.dot += v.dot;
        r.proc += v.proc;
        r.pet += v.pet;
        r.swarm += v.swarm;
        r.other += v.other;
    }

    r.hits += v.count;
    if (v.maxHit > r.maxHit) {
        r.maxHit = v.maxHit;
        r.maxHitWall = v.maxHitWall;
    }
}

static std::string HP_BuildSelectedFightCacheKey()
{
    if (g_dpsSelectedFights.empty()) return std::string();
    std::vector<int> ids;
    ids.reserve(g_dpsSelectedFights.size());
    for (int idx : g_dpsSelectedFights) ids.push_back(idx);
    std::sort(ids.begin(), ids.end());

    std::string key = g_dpsCombinePets ? "pets1:" : "pets0:";
    key.reserve(16 + ids.size() * 5);
    for (int idx : ids) {
        key += std::to_string(idx);
        key.push_back(',');
    }
    return key;
}

static void HP_RecordLiveDpsSpellCast(const std::string& caster, const std::string& spell)
{
    std::string cleanCaster = HP_TrimCopy(caster);
    std::string cleanSpell = HP_TrimCopy(spell);
    if (cleanCaster.empty() || cleanSpell.empty()) return;

    const int64_t now = NowMs();
    std::lock_guard<std::mutex> lk(g_liveDpsMutex);
    // Only save spell casts to the DPS tab while a fight is actually active.
    // This prevents idle/buff/utility spells from showing in Top Spells, and
    // keeps the saved spell list tied to the selected fight.
    if (g_liveDps.mob.empty() || g_liveDps.total == 0 || (now - g_liveDps.lastDamageMs) > kLiveDpsTimeoutMs)
        return;

    g_liveDps.spellCasts[cleanSpell] += 1;
    g_liveDps.spellCastsByCaster[cleanCaster][cleanSpell] += 1;
}

static std::unordered_map<std::string, uint32_t> HP_GetSelectedDpsSpellCasts()
{
    if (!g_dpsSelectedFights.empty()) {
        static std::string s_cachedKey;
        static std::unordered_map<std::string, uint32_t> s_cachedSpells;
        std::string key = HP_BuildSelectedFightCacheKey() + "|spells";
        if (key == s_cachedKey) return s_cachedSpells;

        std::unordered_map<std::string, uint32_t> out;
        std::lock_guard<std::mutex> hk(g_completedDpsMutex);
        for (int idx : g_dpsSelectedFights) {
            if (idx < 0 || idx >= (int)g_completedDpsFights.size()) continue;
            const auto& spells = g_completedDpsFights[(size_t)idx].spellCasts;
            for (const auto& kv : spells) {
                if (!kv.first.empty() && kv.second > 0)
                    out[kv.first] += kv.second;
            }
        }
        s_cachedKey = key;
        s_cachedSpells = out;
        return out;
    }

    int selected = g_fullUiDpsSelectedFight.load();
    if (selected >= 0) {
        std::lock_guard<std::mutex> hk(g_completedDpsMutex);
        if (selected < (int)g_completedDpsFights.size())
            return g_completedDpsFights[(size_t)selected].spellCasts;
        return {};
    }

    std::lock_guard<std::mutex> lk(g_liveDpsMutex);
    return g_liveDps.spellCasts;
}

static std::unordered_map<std::string, std::unordered_map<std::string, uint32_t>> HP_GetSelectedDpsSpellCastsByCaster()
{
    if (!g_dpsSelectedFights.empty()) {
        static std::string s_cachedKey;
        static std::unordered_map<std::string, std::unordered_map<std::string, uint32_t>> s_cachedByCaster;
        std::string key = HP_BuildSelectedFightCacheKey() + "|spellsByCaster";
        if (key == s_cachedKey) return s_cachedByCaster;

        std::unordered_map<std::string, std::unordered_map<std::string, uint32_t>> out;
        std::lock_guard<std::mutex> hk(g_completedDpsMutex);
        for (int idx : g_dpsSelectedFights) {
            if (idx < 0 || idx >= (int)g_completedDpsFights.size()) continue;
            const auto& byCaster = g_completedDpsFights[(size_t)idx].spellCastsByCaster;
            for (const auto& ckv : byCaster) {
                if (ckv.first.empty()) continue;
                for (const auto& skv : ckv.second) {
                    if (!skv.first.empty() && skv.second > 0)
                        out[ckv.first][skv.first] += skv.second;
                }
            }
        }
        s_cachedKey = key;
        s_cachedByCaster = out;
        return out;
    }

    int selected = g_fullUiDpsSelectedFight.load();
    if (selected >= 0) {
        std::lock_guard<std::mutex> hk(g_completedDpsMutex);
        if (selected < (int)g_completedDpsFights.size())
            return g_completedDpsFights[(size_t)selected].spellCastsByCaster;
        return {};
    }

    std::lock_guard<std::mutex> lk(g_liveDpsMutex);
    return g_liveDps.spellCastsByCaster;
}


static std::vector<HPPcDeathRow> HP_GetSelectedDeaths()
{
    std::vector<HPPcDeathRow> out;
    int selected = g_fullUiDpsSelectedFight.load();

    if (!g_dpsSelectedFights.empty()) {
        static std::string s_cachedKey;
        static std::vector<HPPcDeathRow> s_cachedDeaths;
        std::string key = HP_BuildSelectedFightCacheKey();
        if (key == s_cachedKey) return s_cachedDeaths;

        std::lock_guard<std::mutex> hk(g_completedDpsMutex);
        for (int idx : g_dpsSelectedFights) {
            if (idx >= 0 && idx < (int)g_completedDpsFights.size()) {
                const auto& ds = g_completedDpsFights[(size_t)idx].deaths;
                out.insert(out.end(), ds.begin(), ds.end());
            }
        }
        std::sort(out.begin(), out.end(), [](const HPPcDeathRow& a, const HPPcDeathRow& b){ return a.ms < b.ms; });
        s_cachedKey = key;
        s_cachedDeaths = out;
        return out;
    }

    std::lock_guard<std::mutex> hk(g_completedDpsMutex);
    if (selected >= 0 && selected < (int)g_completedDpsFights.size()) {
        out = g_completedDpsFights[(size_t)selected].deaths;
    }
    std::sort(out.begin(), out.end(), [](const HPPcDeathRow& a, const HPPcDeathRow& b){ return a.ms < b.ms; });
    return out;
}

static std::vector<HP_DpsUiRow> HP_GetLiveDpsRows(uint64_t& total, std::string& mob, int& dur)
{
    HP_MaybeArchiveTimedOutLiveDps();
    std::vector<HP_DpsUiRow> out;
    int64_t now = NowMs();
    total = 0; dur = 0; mob = "No active fight";

    const int selected = g_fullUiDpsSelectedFight.load();
    if (!g_dpsSelectedFights.empty()) {
        static std::string s_cachedKey;
        static std::vector<HP_DpsUiRow> s_cachedRows;
        static uint64_t s_cachedTotal = 0;
        static std::string s_cachedMob;
        static int s_cachedDur = 1;

        std::string key = HP_BuildSelectedFightCacheKey();
        if (key == s_cachedKey) {
            total = s_cachedTotal;
            mob = s_cachedMob;
            dur = s_cachedDur;
            return s_cachedRows;
        }

        std::unordered_map<std::string, HP_DpsUiRow> acc;
        int64_t minStart = 0, maxEnd = 0;
        int count = 0;
        std::lock_guard<std::mutex> hk(g_completedDpsMutex);
        for (int idx : g_dpsSelectedFights) {
            if (idx < 0 || idx >= (int)g_completedDpsFights.size()) continue;
            const auto& f = g_completedDpsFights[(size_t)idx];
            total += f.total;
            if (minStart == 0 || f.startedMs < minStart) minStart = f.startedMs;
            if (f.endedMs > maxEnd) maxEnd = f.endedMs;
            for (const auto& kv : f.players) {
                std::string rowName = HP_GetPetCombinedDisplayName(kv.first);
                if (HP_ShouldHideDpsDisplayRow(rowName, f.mob)) continue;
                const bool sourceWasCombinedPet = (g_dpsCombinePets && !HP_SameNameNoCase(rowName, kv.first));
                HP_AddRowToDpsAccumulator(acc, rowName, kv.second, sourceWasCombinedPet);
            }
            ++count;
        }
        mob = count == 1 ? "Selected Fight" : (std::to_string(count) + " selected fights");
        dur = (minStart > 0 && maxEnd > minStart) ? (int)std::max<int64_t>(1, (maxEnd - minStart) / 1000) : 1;
        out.reserve(acc.size());
        for (auto& kv : acc) out.push_back(kv.second);
        s_cachedKey = key;
        s_cachedRows = out;
        s_cachedTotal = total;
        s_cachedMob = mob;
        s_cachedDur = dur;
    } else if (selected >= 0) {
        std::lock_guard<std::mutex> hk(g_completedDpsMutex);
        if (selected < (int)g_completedDpsFights.size()) {
            const auto& f = g_completedDpsFights[(size_t)selected];
            mob = f.mob;
            total = f.total;
            dur = (int)std::max<int64_t>(1, (f.endedMs - f.startedMs) / 1000);
            std::unordered_map<std::string, HP_DpsUiRow> acc;
            for (const auto& kv : f.players) {
                std::string rowName = HP_GetPetCombinedDisplayName(kv.first);
                if (HP_ShouldHideDpsDisplayRow(rowName, f.mob)) continue;
                const bool sourceWasCombinedPet = (g_dpsCombinePets && !HP_SameNameNoCase(rowName, kv.first));
                HP_AddRowToDpsAccumulator(acc, rowName, kv.second, sourceWasCombinedPet);
            }
            out.reserve(acc.size());
            for (auto& akv : acc) out.push_back(akv.second);
        }
    } else {
        std::lock_guard<std::mutex> lk(g_liveDpsMutex);
        if (!g_liveDps.mob.empty() && (now - g_liveDps.lastDamageMs) <= kLiveDpsTimeoutMs) {
            mob = g_liveDps.mob;
            total = g_liveDps.total;
            dur = (int)std::max<int64_t>(1, (now - g_liveDps.startedMs) / 1000);
            std::unordered_map<std::string, HP_DpsUiRow> acc;
            for (const auto& kv : g_liveDps.players) {
                std::string rowName = HP_GetPetCombinedDisplayName(kv.first);
                if (HP_ShouldHideDpsDisplayRow(rowName, g_liveDps.mob)) continue;
                const bool sourceWasCombinedPet = (g_dpsCombinePets && !HP_SameNameNoCase(rowName, kv.first));
                HP_AddRowToDpsAccumulator(acc, rowName, kv.second, sourceWasCombinedPet);
            }
            out.reserve(acc.size());
            for (auto& akv : acc) out.push_back(akv.second);
        }
    }

    {
        uint64_t displayTotal = 0;
        for (const auto& r : out) displayTotal += r.dmg;
        if (displayTotal > 0) total = displayTotal;
    }
    std::sort(out.begin(), out.end(), [](const HP_DpsUiRow& a, const HP_DpsUiRow& b) { return a.dmg > b.dmg; });
    if (out.size() > 30) out.resize(30);
    return out;
}



static bool HP_ParseDateMDY(const std::string& s, int* outM, int* outD, int* outY)
{
    if (!outM || !outD || !outY) return false;
    int m = 0, d = 0, y = 0;
    if (sscanf_s(s.c_str(), "%d/%d/%d", &m, &d, &y) != 3) return false;
    if (m < 1 || m > 12 || d < 1 || d > 31 || y < 1970 || y > 2500) return false;
    *outM = m; *outD = d; *outY = y;
    return true;
}

static int HP_DaysInMonth(int month, int year)
{
    static const int days[] = { 31,28,31,30,31,30,31,31,30,31,30,31 };
    if (month < 1 || month > 12) return 30;
    if (month == 2) {
        bool leap = ((year % 4 == 0) && (year % 100 != 0)) || (year % 400 == 0);
        return leap ? 29 : 28;
    }
    return days[month - 1];
}

static int HP_FirstWeekdayOfMonth(int month, int year)
{
    std::tm tmv{};
    tmv.tm_year = year - 1900;
    tmv.tm_mon = month - 1;
    tmv.tm_mday = 1;
    tmv.tm_hour = 12;
    std::mktime(&tmv);
    return tmv.tm_wday; // 0 = Sunday
}

static std::string HP_FormatMDY(int month, int day, int year)
{
    char buf[32] = { 0 };
    std::snprintf(buf, sizeof(buf), "%02d/%02d/%04d", month, day, year);
    return std::string(buf);
}

static void HP_GetTodayMDY(int* outM, int* outD, int* outY)
{
    std::time_t now = std::time(nullptr);
    std::tm lt{};
#ifdef _WIN32
    localtime_s(&lt, &now);
#else
    lt = *std::localtime(&now);
#endif
    if (outM) *outM = lt.tm_mon + 1;
    if (outD) *outD = lt.tm_mday;
    if (outY) *outY = lt.tm_year + 1900;
}

static bool HP_DatePopupButton(const char* id, const char* preview, const std::vector<std::string>& dates, char* outBuf, size_t outBufSize, float width)
{
    bool changed = false;
    HP_LoadCalIconTextureIfNeeded();

    std::string shown = (preview && preview[0]) ? preview : "Any";
    std::string buttonId = std::string("##") + id;
    if (ImGui::Button(buttonId.c_str(), ImVec2(width, 24.0f))) {
        ImGui::OpenPopup(id);
    }

    // Draw the optional Cal.png inside the button. If the image is missing,
    // use simple text instead of the unsupported emoji/question-mark glyph.
    ImDrawList* dl = ImGui::GetWindowDrawList();
    ImVec2 bpMin = ImGui::GetItemRectMin();
    ImVec2 bpMax = ImGui::GetItemRectMax();
    float iconSize = 16.0f;
    float textW = ImGui::CalcTextSize(shown.c_str()).x;
    float totalW = textW + 8.0f + iconSize;
    float startX = bpMin.x + std::max(6.0f, (width - totalW) * 0.5f);
    float y = bpMin.y + (24.0f - iconSize) * 0.5f;
    if (g_calIconTexture.id) {
        dl->AddImage(g_calIconTexture.id, ImVec2(startX, y), ImVec2(startX + iconSize, y + iconSize));
    } else {
        dl->AddText(ImVec2(startX, bpMin.y + 4.0f), IM_COL32(170, 210, 255, 255), "Cal");
        startX += ImGui::CalcTextSize("Cal").x - iconSize;
    }
    dl->AddText(ImVec2(startX + iconSize + 8.0f, bpMin.y + 4.0f), ImGui::GetColorU32(ImGuiCol_Text), shown.c_str());

    if (ImGui::BeginPopup(id)) {
        static std::unordered_map<std::string, int> popupMonth;
        static std::unordered_map<std::string, int> popupYear;

        int m = 0, d = 0, yv = 0;
        if (!HP_ParseDateMDY(shown, &m, &d, &yv)) HP_GetTodayMDY(&m, &d, &yv);

        std::string key = id ? id : "date";
        if (popupMonth.find(key) == popupMonth.end()) {
            popupMonth[key] = m;
            popupYear[key] = yv;
        }

        int& curM = popupMonth[key];
        int& curY = popupYear[key];

        if (ImGui::Selectable("Any", shown == "Any")) {
            if (outBuf && outBufSize > 0) outBuf[0] = 0;
            changed = true;
            ImGui::CloseCurrentPopup();
        }

        ImGui::Separator();

        static const char* monthNames[] = {
            "January","February","March","April","May","June",
            "July","August","September","October","November","December"
        };

        if (ImGui::Button("<", ImVec2(30.0f, 24.0f))) {
            --curM;
            if (curM < 1) { curM = 12; --curY; }
        }
        ImGui::SameLine();
        ImGui::Text("%s %d", monthNames[std::max(0, std::min(11, curM - 1))], curY);
        ImGui::SameLine(ImGui::GetWindowWidth() - 44.0f);
        if (ImGui::Button(">", ImVec2(30.0f, 24.0f))) {
            ++curM;
            if (curM > 12) { curM = 1; ++curY; }
        }

        const char* wk[] = { "Su", "Mo", "Tu", "We", "Th", "Fr", "Sa" };
        if (ImGui::BeginTable((std::string("##calgrid_") + key).c_str(), 7, ImGuiTableFlags_SizingFixedFit)) {
            for (int c = 0; c < 7; ++c) {
                ImGui::TableNextColumn();
                ImGui::TextDisabled("%s", wk[c]);
            }

            int first = HP_FirstWeekdayOfMonth(curM, curY);
            int days = HP_DaysInMonth(curM, curY);
            int cell = 0;
            for (int row = 0; row < 6; ++row) {
                ImGui::TableNextRow();
                for (int col = 0; col < 7; ++col, ++cell) {
                    ImGui::TableNextColumn();
                    int day = cell - first + 1;
                    if (day < 1 || day > days) {
                        ImGui::TextDisabled(" ");
                        continue;
                    }
                    std::string dateStr = HP_FormatMDY(curM, day, curY);
                    bool selected = (shown == dateStr);
                    if (ImGui::Selectable((std::to_string(day) + "##" + key + dateStr).c_str(), selected, 0, ImVec2(28.0f, 22.0f))) {
                        std::snprintf(outBuf, outBufSize, "%s", dateStr.c_str());
                        changed = true;
                        ImGui::CloseCurrentPopup();
                    }
                }
            }
            ImGui::EndTable();
        }

        ImGui::EndPopup();
    }
    return changed;
}

static void HP_DrawDpsFightList(float w)
{
    HP_MaybeArchiveTimedOutLiveDps();
    ImGui::BeginChild("##dps_left_column", ImVec2(w, 0), false);

    std::vector<CompletedDpsFight> fights;
    { std::lock_guard<std::mutex> hk(g_completedDpsMutex); fights = g_completedDpsFights; }

    std::vector<int> visible;
    visible.reserve(fights.size());
    for (int i = 0; i < (int)fights.size(); ++i) {
        if (HP_FightPassesDpsFilters(fights[(size_t)i])) visible.push_back(i);
    }

    // The selected set must always match the current filtered/visible fight list.
    // This makes SELECT ALL mean "select all fights currently showing" only.
    // Hidden fights from older dates/search filters are removed automatically.
    std::unordered_set<int> visibleSet;
    visibleSet.reserve(visible.size());
    for (int idx : visible) visibleSet.insert(idx);
    for (auto it = g_dpsSelectedFights.begin(); it != g_dpsSelectedFights.end(); ) {
        if (visibleSet.count(*it) == 0) it = g_dpsSelectedFights.erase(it);
        else ++it;
    }
    const bool allVisibleSelected = !visible.empty() && g_dpsSelectedFights.size() == visible.size();

    // Keep the fight search / range / select-all controls outside the scrolling
    // fight list so they stay pinned at the top while the mob list scrolls.
    ImGui::BeginChild("##dps_fight_header", ImVec2(w, 108.0f), true, ImGuiWindowFlags_NoScrollbar | ImGuiWindowFlags_NoScrollWithMouse);
    ImGui::TextColored(ImVec4(0.32f, 0.72f, 1.0f, 1.0f), "FIGHTS (%d/%d Selected)", (int)g_dpsSelectedFights.size(), (int)visible.size());
    ImGui::Separator();
    float searchAvail = ImGui::GetContentRegionAvail().x;
    ImGui::SetNextItemWidth(std::max(120.0f, searchAvail - 40.0f));
    ImGui::InputTextWithHint("##fight_search", "Search fights...", g_dpsMobSearch, IM_ARRAYSIZE(g_dpsMobSearch));
    ImGui::SameLine(0.0f, 6.0f);
    ImGui::Button("⌄", ImVec2(32.0f, 24.0f));

    ImGui::Spacing();
    const float btnGap = 5.0f;
    float buttonsAvail = ImGui::GetContentRegionAvail().x;
    const float btnW = std::max(70.0f, (buttonsAvail - btnGap) / 2.0f);
    if (ImGui::Button(g_dpsRangeMode ? "RANGE ON" : "SELECT RANGE", ImVec2(btnW, 24.0f))) {
        g_dpsRangeMode = !g_dpsRangeMode;
        g_dpsRangeStart = -1;
        g_dpsSelectAllToggle = false;
    }
    ImGui::SameLine(0, btnGap);
    if (ImGui::Button(allVisibleSelected ? "UNSELECT" : "SELECT ALL", ImVec2(btnW, 24.0f))) {
        g_dpsSelectedFights.clear();
        if (!allVisibleSelected) {
            // Select ONLY fights that pass the current filters/search/date range.
            // Hidden fights are intentionally not included.
            for (int idx : visible)
                g_dpsSelectedFights.insert(idx);
            if (!visible.empty()) g_fullUiDpsSelectedFight.store(visible.front());
        }
        g_dpsSelectAllToggle = !g_dpsSelectedFights.empty();
        g_dpsRangeMode = false;
        g_dpsRangeStart = -1;
    }
    ImGui::EndChild();

    ImGui::BeginChild("##dps_fight_list", ImVec2(w, -414.0f), true, ImGuiWindowFlags_AlwaysVerticalScrollbar);

    bool liveActive = false;
    std::string liveMob = "Current Fight";
    uint64_t liveTotal = 0;
    int liveDur = 0;
    {
        std::lock_guard<std::mutex> lk(g_liveDpsMutex);
        const int64_t now = NowMs();
        liveActive = (!g_liveDps.mob.empty() && (now - g_liveDps.lastDamageMs) <= kLiveDpsTimeoutMs);
        if (liveActive) {
            liveMob = g_liveDps.mob;
            liveTotal = g_liveDps.total;
            liveDur = (int)std::max<int64_t>(1, (now - g_liveDps.startedMs) / 1000);
        }
    }

    ImGui::Spacing();
    if (liveActive && HP_ContainsNoCase(liveMob, g_dpsMobSearch)) {
        ImGui::PushStyleColor(ImGuiCol_Text, IM_COL32(100, 200, 255, 255));
        if (ImGui::Selectable((std::string("LIVE: ") + liveMob).c_str(), g_fullUiDpsSelectedFight.load() < 0)) {
            g_dpsSelectedFights.clear();
            g_fullUiDpsSelectedFight.store(-1);
            g_fullUiDpsSelectedPlayer.clear();
        }
        ImGui::PopStyleColor();
        ImGui::TextDisabled("  %s  @%s  %02d:%02d", HT_FormatShort(liveTotal).c_str(), HT_FormatInteger(liveDur ? liveTotal/(uint64_t)liveDur : 0).c_str(), liveDur/60, liveDur%60);
    }

    if (fights.empty()) {
        ImGui::TextDisabled("No completed fights yet.");
    } else {
        int shown = 0;
        for (int idx : visible) {
            const auto& f = fights[(size_t)idx];
            int fdur = (int)std::max<int64_t>(1, (f.endedMs - f.startedMs) / 1000);
            bool selected = g_dpsSelectedFights.empty() ? (g_fullUiDpsSelectedFight.load() == idx) : (g_dpsSelectedFights.count(idx) != 0);

            // Compact two-line fight row: mob + time on the first line, date/duration/total underneath.
            // This keeps the left panel the same size, but squeezes the contents so nothing gets clipped.
            ImVec2 rowPos = ImGui::GetCursorScreenPos();
            float rowW = ImGui::GetContentRegionAvail().x - 2.0f;
            float rowH = 52.0f;
            std::string rowId = "##fightrow" + std::to_string(idx);
            if (ImGui::Selectable(rowId.c_str(), selected, 0, ImVec2(rowW, rowH))) {
                if (g_dpsRangeMode) {
                    if (g_dpsRangeStart < 0) {
                        g_dpsRangeStart = idx;
                        g_dpsSelectedFights.clear();
                        g_dpsSelectedFights.insert(idx);
                    } else {
                        int a = std::min(g_dpsRangeStart, idx);
                        int b = std::max(g_dpsRangeStart, idx);
                        g_dpsSelectedFights.clear();
                        for (int vi : visible) if (vi >= a && vi <= b) g_dpsSelectedFights.insert(vi);
                        g_dpsRangeMode = false;
                        g_dpsRangeStart = -1;
                    }
                } else {
                    g_dpsSelectedFights.clear();
                    g_dpsSelectAllToggle = false;
                    g_fullUiDpsSelectedFight.store(idx);
                }
                g_fullUiDpsSelectedPlayer.clear();
            }

            ImDrawList* dl = ImGui::GetWindowDrawList();
            ImU32 mobColor = selected ? IM_COL32(245, 250, 255, 255) : IM_COL32(230, 238, 248, 255);
            ImU32 subColor = selected ? IM_COL32(205, 220, 245, 235) : IM_COL32(145, 155, 175, 230);
            ImU32 timeColor = selected ? IM_COL32(215, 225, 245, 245) : IM_COL32(160, 168, 185, 230);

            const float iconSize = 30.0f;
            const float iconX = rowPos.x + 8.0f;
            const float textX = rowPos.x + 46.0f;
            HP_DrawMobIconInList(dl, ImVec2(iconX, rowPos.y + 11.0f), iconSize, f.mobRace, f.mobBodyType, f.mobIconKey, f.mob);

            std::string mobText = f.mob;
            std::string timeText = HP_FormatTimeOnly(f.wallEnded);
            std::string subText = HP_FormatDateTimeLong(f.wallEnded > 0 ? f.wallEnded : f.wallStarted) + "  •  " +
                (fdur < 3600 ? (std::to_string(fdur / 60) + ":" + (fdur % 60 < 10 ? "0" : "") + std::to_string(fdur % 60)) : (std::to_string(fdur) + "s")) +
                "  •  " + HT_FormatShort(f.total);

            // Trim mob text if it would collide with the right-aligned time.
            float availableMobW = std::max(80.0f, rowW - (textX - rowPos.x) - ImGui::CalcTextSize(timeText.c_str()).x - 20.0f);
            std::string originalMobText = mobText;
            while (!mobText.empty() && ImGui::CalcTextSize(mobText.c_str()).x > availableMobW) {
                mobText.pop_back();
            }
            if (mobText != originalMobText && mobText.size() > 3) {
                mobText.replace(mobText.size() - 3, 3, "...");
            }

            dl->AddText(ImVec2(textX, rowPos.y + 7.0f), mobColor, mobText.c_str());
            ImVec2 ts = ImGui::CalcTextSize(timeText.c_str());
            dl->AddText(ImVec2(rowPos.x + rowW - ts.x - 10.0f, rowPos.y + 7.0f), timeColor, timeText.c_str());
            dl->AddText(ImVec2(textX, rowPos.y + 30.0f), subColor, subText.c_str());

            if (++shown >= 100) break;
        }
        if ((int)visible.size() > 100) {
            ImGui::Button("LOAD MORE", ImVec2(w - 18.0f, 24.0f));
        }
    }
    ImGui::EndChild();

    ImGui::Spacing();
    ImGui::BeginChild("##dps_filters", ImVec2(w, 326.0f), true, ImGuiWindowFlags_NoScrollbar | ImGuiWindowFlags_NoScrollWithMouse);
    ImGui::TextColored(ImVec4(0.32f, 0.72f, 1.0f, 1.0f), "FILTERS");
    ImGui::Separator();

    std::vector<std::string> dates;
    dates.push_back("Any");
    {   std::unordered_set<std::string> seen;
        for (const auto& f : fights) {
            std::string d = HP_FormatDateOnly(f.wallEnded > 0 ? f.wallEnded : f.wallStarted);
            if (d != "Unknown" && seen.insert(d).second) dates.push_back(d);
        }
        std::sort(dates.begin() + 1, dates.end());
    }

    ImGui::TextDisabled("DATE RANGE");
    float dateAvail = ImGui::GetContentRegionAvail().x - 4.0f;
    float dateW = std::max(94.0f, (dateAvail - 8.0f) * 0.5f);
    if (ImGui::BeginTable("##date_range_even_table", 2, ImGuiTableFlags_SizingStretchSame)) {
        ImGui::TableSetupColumn("From", ImGuiTableColumnFlags_WidthStretch);
        ImGui::TableSetupColumn("To", ImGuiTableColumnFlags_WidthStretch);

        ImGui::TableNextRow();
        ImGui::TableNextColumn();
        ImGui::TextDisabled("From");
        ImGui::TableNextColumn();
        ImGui::TextDisabled("To");

        ImGui::TableNextRow();
        ImGui::TableNextColumn();
        const char* fromLabel = g_dpsDateFrom[0] ? g_dpsDateFrom : "Any";
        float fromW = std::max(94.0f, ImGui::GetContentRegionAvail().x);
        HP_DatePopupButton("date_from_popup", fromLabel, dates, g_dpsDateFrom, sizeof(g_dpsDateFrom), fromW);

        ImGui::TableNextColumn();
        const char* toLabel = g_dpsDateTo[0] ? g_dpsDateTo : "Any";
        float toW = std::max(94.0f, ImGui::GetContentRegionAvail().x);
        HP_DatePopupButton("date_to_popup", toLabel, dates, g_dpsDateTo, sizeof(g_dpsDateTo), toW);

        ImGui::EndTable();
    }

    static const char* durLabels[] = { "Any", "Under 30 sec", "30-60 sec", "1-2 min", "Over 2 min" };
    ImGui::TextDisabled("DURATION");
    ImGui::SetNextItemWidth(ImGui::GetContentRegionAvail().x - 4.0f);
    if (ImGui::BeginCombo("##duration_filter", durLabels[g_dpsDurationFilter])) {
        for (int i = 0; i < 5; ++i) {
            if (ImGui::Selectable(durLabels[i], g_dpsDurationFilter == i)) g_dpsDurationFilter = i;
        }
        ImGui::EndCombo();
    }

    ImGui::TextDisabled("MIN DAMAGE");
    ImGui::SetNextItemWidth(ImGui::GetContentRegionAvail().x - 4.0f);
    ImGui::InputInt("##mindamage", &g_dpsMinDamageFilter, 0, 0);
    if (g_dpsMinDamageFilter < 0) g_dpsMinDamageFilter = 0;

    ImGui::TextDisabled("GROUP");
    ImGui::SetNextItemWidth(ImGui::GetContentRegionAvail().x - 4.0f);
    if (ImGui::BeginCombo("##group_filter", g_dpsGroupFilter[0] ? g_dpsGroupFilter : "All Groups")) {
        const char* opts[] = { "All Groups", "Group 1", "Group 2", "Group 3", "Group 4", "Group 5", "Group 6", "Raid" };
        for (auto opt : opts) {
            if (ImGui::Selectable(opt, std::strcmp(g_dpsGroupFilter, opt) == 0))
                std::snprintf(g_dpsGroupFilter, sizeof(g_dpsGroupFilter), "%s", opt);
        }
        ImGui::EndCombo();
    }

    if (ImGui::Button("Clear Filters", ImVec2(ImGui::GetContentRegionAvail().x - 4.0f, 24.0f))) {
        g_dpsMobSearch[0] = 0;
        g_dpsDateFrom[0] = 0;
        g_dpsDateTo[0] = 0;
        g_dpsMinDamageFilter = 0;
        g_dpsDurationFilter = 0;
        std::snprintf(g_dpsGroupFilter, sizeof(g_dpsGroupFilter), "All Groups");
    }
    ImGui::EndChild();
    ImGui::EndChild();
}

static void HP_DrawDpsTypeBar(const char* label, uint64_t value, uint64_t total, ImU32 color, float barW)
{
    float f = total > 0 ? (float)((double)value / (double)total) : 0.0f;
    if (f < 0.0f) f = 0.0f;
    if (f > 1.0f) f = 1.0f;
    ImGui::Text("%s", label);
    ImGui::SameLine(86.0f);
    ImGui::Text("%s", HT_FormatShort(value).c_str());
    ImGui::SameLine(158.0f);
    ImGui::Text("%.1f%%", total > 0 ? (double)value * 100.0 / (double)total : 0.0);
    ImVec2 p = ImGui::GetCursorScreenPos();
    ImDrawList* dl = ImGui::GetWindowDrawList();
    dl->AddRectFilled(p, ImVec2(p.x + barW, p.y + 6), IM_COL32(14, 22, 38, 230), 3.0f);
    if (value > 0) dl->AddRectFilled(p, ImVec2(p.x + barW * f, p.y + 6), color, 3.0f);
    ImGui::Dummy(ImVec2(barW, 10));
}



static void HP_DrawDpsTypeStackBar(const HP_DpsUiRow& r, float width, float height)
{
    uint64_t vals[6] = { r.melee, r.spell, r.dot, r.proc, r.pet + r.swarm, r.other };
    ImU32 cols[6] = {
        IM_COL32(40,130,255,255),   // melee
        IM_COL32(145,80,255,255),   // spell
        IM_COL32(255,115,30,255),   // dot
        IM_COL32(255,190,60,255),   // proc
        IM_COL32(70,210,120,255),   // pet/swarm
        IM_COL32(130,145,165,255)   // other
    };
    ImVec2 p = ImGui::GetCursorScreenPos();
    ImDrawList* dl = ImGui::GetWindowDrawList();
    dl->AddRectFilled(p, ImVec2(p.x + width, p.y + height), IM_COL32(9, 18, 34, 230), height * 0.5f);
    float x = p.x;
    for (int i = 0; i < 6; ++i) {
        if (vals[i] == 0 || r.dmg == 0) continue;
        float seg = std::max(2.0f, width * (float)((double)vals[i] / (double)r.dmg));
        if (x + seg > p.x + width) seg = (p.x + width) - x;
        if (seg <= 0.0f) break;
        dl->AddRectFilled(ImVec2(x, p.y), ImVec2(x + seg, p.y + height), cols[i], height * 0.5f);
        x += seg;
        if (x >= p.x + width) break;
    }
    dl->AddRect(p, ImVec2(p.x + width, p.y + height), IM_COL32(48, 126, 235, 90), height * 0.5f, 0, 1.0f);
    ImGui::Dummy(ImVec2(width, height));
    if (ImGui::IsItemHovered()) {
        ImGui::BeginTooltip();
        ImGui::Text("Melee: %s", HT_FormatShort(r.melee).c_str());
        ImGui::Text("Spell: %s", HT_FormatShort(r.spell).c_str());
        ImGui::Text("DoT: %s", HT_FormatShort(r.dot).c_str());
        ImGui::Text("Proc: %s", HT_FormatShort(r.proc).c_str());
        ImGui::Text("Pet: %s", HT_FormatShort(r.pet + r.swarm).c_str());
        ImGui::Text("Other: %s", HT_FormatShort(r.other).c_str());
        ImGui::EndTooltip();
    }
}

static void HP_DrawDpsHeroStat(const char* title, const char* value, const char* sub, ImU32 accent, float w, HP_IconTexture* cornerIcon = nullptr)
{
    ImVec2 pos = ImGui::GetCursorScreenPos();
    ImDrawList* dl = ImGui::GetWindowDrawList();
    ImVec2 size(w, 66.0f);
    dl->AddRectFilled(pos, ImVec2(pos.x + size.x, pos.y + size.y), IM_COL32(5, 10, 22, 230), 8.0f);
    dl->AddRect(pos, ImVec2(pos.x + size.x, pos.y + size.y), IM_COL32(48, 125, 230, 150), 8.0f, 0, 1.1f);
    dl->AddRectFilled(pos, ImVec2(pos.x + 4.0f, pos.y + size.y), accent, 8.0f);
    if (cornerIcon && cornerIcon->id) {
        const float iconSz = 26.0f;
        ImVec2 ip(pos.x + size.x - iconSz - 10.0f, pos.y + 8.0f);
        dl->AddImage(cornerIcon->id, ip, ImVec2(ip.x + iconSz, ip.y + iconSz));
    }
    ImGui::Dummy(size);
    ImGui::SetCursorScreenPos(ImVec2(pos.x + 14.0f, pos.y + 9.0f));
    ImGui::PushStyleColor(ImGuiCol_Text, accent);
    ImGui::TextUnformatted(value);
    ImGui::PopStyleColor();
    ImGui::SetCursorScreenPos(ImVec2(pos.x + 14.0f, pos.y + 35.0f));
    ImGui::TextDisabled("%s", title);
    if (sub && sub[0]) {
        ImGui::SetCursorScreenPos(ImVec2(pos.x + 14.0f, pos.y + 50.0f));
        ImGui::TextDisabled("%s", sub);
    }
}

static void HP_DrawDpsMiniGraph(const std::vector<HP_DpsUiRow>& rows, uint64_t total, float w, float h, int durationSec = 0, const char* statLabel = "DPS")
{
    ImVec2 pos = ImGui::GetCursorScreenPos();
    ImDrawList* dl = ImGui::GetWindowDrawList();
    dl->AddRectFilled(pos, ImVec2(pos.x + w, pos.y + h), IM_COL32(3, 8, 18, 225), 8.0f);
    dl->AddRect(pos, ImVec2(pos.x + w, pos.y + h), IM_COL32(42, 105, 210, 150), 8.0f, 0, 1.0f);

    const float leftPad = 56.0f;
    const float rightPad = 16.0f;
    const float topPad = 14.0f;
    const float bottomPad = 28.0f;
    ImVec2 gp0(pos.x + leftPad, pos.y + topPad);
    ImVec2 gp1(pos.x + w - rightPad, pos.y + h - bottomPad);
    if (gp1.x <= gp0.x + 20.0f || gp1.y <= gp0.y + 20.0f) {
        ImGui::Dummy(ImVec2(w, h));
        return;
    }

    int graphDuration = std::max(1, durationSec);

    // Safety: some older paths can accidentally hand this function milliseconds
    // instead of seconds. If the duration is clearly impossible for an EQ fight,
    // convert it down so labels become normal M:SS instead of huge second counts.
    if (graphDuration > 86400)
        graphDuration = std::max(1, graphDuration / 1000);

    uint64_t avgRate = (graphDuration > 0) ? total / (uint64_t)graphDuration : 0;

    // Build an adaptive rate scale.  No fixed 70s / 100k cap: the X axis uses
    // the full fight duration and the Y axis scales from the selected fight.
    uint64_t maxPlayerRate = 0;
    for (const auto& r : rows) {
        uint64_t pr = (graphDuration > 0) ? r.dmg / (uint64_t)graphDuration : 0;
        if (pr > maxPlayerRate) maxPlayerRate = pr;
    }
    uint64_t axisMax = std::max<uint64_t>(1, std::max<uint64_t>(avgRate * 2, maxPlayerRate * 2));
    if (axisMax < avgRate + avgRate / 3) axisMax = avgRate + avgRate / 3 + 1;

    auto niceAxis = [](uint64_t v) -> uint64_t {
        if (v <= 10) return 10;
        uint64_t pow10 = 1;
        while (pow10 * 10 < v) pow10 *= 10;
        uint64_t n = (v + pow10 - 1) / pow10;
        if (n <= 2) n = 2;
        else if (n <= 5) n = 5;
        else n = 10;
        return n * pow10;
    };
    axisMax = niceAxis(axisMax);

    auto formatAxis = [](uint64_t v) -> std::string {
        if (v >= 1000000) {
            char b[32]; std::snprintf(b, sizeof(b), "%.1fm", (double)v / 1000000.0); return b;
        }
        if (v >= 1000) {
            char b[32]; std::snprintf(b, sizeof(b), "%uk", (unsigned)(v / 1000)); return b;
        }
        return std::to_string(v);
    };

    // Axes + grid.
    dl->AddLine(ImVec2(gp0.x, gp0.y), ImVec2(gp0.x, gp1.y), IM_COL32(120, 150, 190, 90), 1.0f);
    dl->AddLine(ImVec2(gp0.x, gp1.y), ImVec2(gp1.x, gp1.y), IM_COL32(120, 150, 190, 90), 1.0f);

    for (int i = 0; i <= 5; ++i) {
        float t = (float)i / 5.0f;
        float y = gp0.y + (gp1.y - gp0.y) * t;
        dl->AddLine(ImVec2(gp0.x, y), ImVec2(gp1.x, y), IM_COL32(42, 70, 105, i == 5 ? 100 : 65), 1.0f);
        uint64_t labelVal = (uint64_t)((double)axisMax * (1.0 - (double)t));
        std::string yLabel = formatAxis(labelVal);
        dl->AddText(ImVec2(pos.x + 10.0f, y - 7.0f), IM_COL32(170, 180, 200, 220), yLabel.c_str());
    }

    auto formatTime = [graphDuration](int sec) -> std::string {
        // If the whole fight is under 60 seconds, show seconds.
        // Once the fight is 60+ seconds, every tick/tooltip uses M:SS.
        if (graphDuration < 60)
            return std::to_string(sec) + "s";

        int m = sec / 60;
        int s = sec % 60;
        char b[32];
        std::snprintf(b, sizeof(b), "%d:%02d", m, s);
        return b;
    };

    const int timeSteps = 7;
    for (int i = 0; i <= timeSteps; ++i) {
        float t = (float)i / (float)timeSteps;
        float x = gp0.x + (gp1.x - gp0.x) * t;
        dl->AddLine(ImVec2(x, gp0.y), ImVec2(x, gp1.y), IM_COL32(42, 70, 105, 45), 1.0f);
        int tickSec = (int)std::llround((double)graphDuration * (double)t);
        std::string label = formatTime(tickSec);
        ImVec2 ts = ImGui::CalcTextSize(label.c_str());
        dl->AddText(ImVec2(x - ts.x * 0.5f, gp1.y + 7.0f), IM_COL32(170, 180, 200, 220), label.c_str());
    }

    if (rows.empty() || total == 0) {
        ImGui::Dummy(ImVec2(w, h));
        return;
    }

    // Draw line-only graph.  The old blue fill/shaded area was intentionally removed.
    const int n = std::max(36, std::min(360, graphDuration + 1));
    std::vector<float> vals;
    vals.reserve(n);
    float seed = (float)((total % 9973u) / 9973.0f);
    for (int i = 0; i < n; ++i) {
        float t = (float)i / (float)(n - 1);
        float ramp = std::min(1.0f, t * 5.0f);
        float fall = (t > 0.72f) ? (1.0f - (t - 0.72f) * 1.7f) : 1.0f;
        if (fall < 0.10f) fall = 0.10f;
        float wiggle = 0.12f * std::sin((t * 28.0f) + seed * 6.28f) + 0.07f * std::sin((t * 73.0f) + seed * 2.9f);
        float rate = (float)avgRate * (1.0f + wiggle) * ramp * fall;
        if (i == n - 1) rate *= 0.10f;
        if (rate < 0.0f) rate = 0.0f;
        if ((uint64_t)rate > axisMax) rate = (float)axisMax;
        vals.push_back(rate);
    }

    std::vector<ImVec2> poly;
    poly.reserve(vals.size());
    for (size_t i = 0; i < vals.size(); ++i) {
        float x = gp0.x + (gp1.x - gp0.x) * ((float)i / (float)(vals.size() - 1));
        float frac = axisMax > 0 ? std::min(1.0f, vals[i] / (float)axisMax) : 0.0f;
        float y = gp1.y - (gp1.y - gp0.y) * frac;
        poly.push_back(ImVec2(x, y));
    }

    for (size_t i = 1; i < poly.size(); ++i) {
        dl->AddLine(poly[i - 1], poly[i], IM_COL32(25, 145, 255, 255), 2.0f);
    }

    // Real-time hover readout under the cursor.
    ImGui::InvisibleButton("##hp_graph_hover", ImVec2(w, h));
    if (ImGui::IsItemHovered()) {
        ImVec2 mp = ImGui::GetIO().MousePos;
        if (mp.x >= gp0.x && mp.x <= gp1.x && mp.y >= gp0.y && mp.y <= gp1.y && !vals.empty()) {
            float t = (mp.x - gp0.x) / std::max(1.0f, gp1.x - gp0.x);
            t = std::max(0.0f, std::min(1.0f, t));
            float fidx = t * (float)(vals.size() - 1);
            int i0 = (int)std::floor(fidx);
            int i1 = std::min((int)vals.size() - 1, i0 + 1);
            float lt = fidx - (float)i0;
            float v = vals[(size_t)i0] * (1.0f - lt) + vals[(size_t)i1] * lt;
            int sec = (int)std::llround((double)graphDuration * (double)t);
            float y = gp1.y - (gp1.y - gp0.y) * std::min(1.0f, v / (float)axisMax);

            dl->AddLine(ImVec2(mp.x, gp0.y), ImVec2(mp.x, gp1.y), IM_COL32(255, 255, 255, 130), 1.0f);
            dl->AddCircleFilled(ImVec2(mp.x, y), 4.0f, IM_COL32(255, 255, 255, 235), 16);

            ImGui::BeginTooltip();
            ImGui::Text("Time: %s", formatTime(sec).c_str());
            ImGui::Text("%s: %s", statLabel ? statLabel : "Value", HT_FormatInteger((uint64_t)std::max(0.0f, v)).c_str());
            ImGui::EndTooltip();
        }
    }
}
static void HP_DrawDpsDonutFallback(uint64_t melee, uint64_t spell, uint64_t dot, uint64_t petproc, uint64_t other, uint64_t total, float size)
{
    ImVec2 pos = ImGui::GetCursorScreenPos();
    ImDrawList* dl = ImGui::GetWindowDrawList();
    ImVec2 c(pos.x + size * 0.5f, pos.y + size * 0.5f);
    float r = size * 0.38f;
    float thickness = std::max(8.0f, size * 0.14f);
    const float PI = 3.14159265358979323846f;

    dl->AddCircle(c, r, IM_COL32(18, 31, 55, 255), 72, thickness);

    uint64_t values[5] = { melee, spell, dot, petproc, other };
    ImU32 cols[5] = {
        IM_COL32(35,130,255,255),
        IM_COL32(155,75,255,255),
        IM_COL32(255,115,35,255),
        IM_COL32(75,215,115,255),
        IM_COL32(160,175,195,255)
    };

    if (total > 0) {
        float a = -PI * 0.5f;
        for (int i = 0; i < 5; ++i) {
            if (values[i] == 0) continue;
            float span = ((float)((double)values[i] / (double)total)) * (PI * 2.0f);
            float a2 = a + span;
            dl->PathClear();
            dl->PathArcTo(c, r, a, a2, std::max(8, (int)(span * 36.0f)));
            dl->PathStroke(cols[i], false, thickness);
            a = a2;
        }
    }

    dl->AddCircleFilled(c, size * 0.22f, IM_COL32(4, 9, 19, 245), 48);
    dl->AddCircle(c, size * 0.22f, IM_COL32(60, 135, 255, 110), 48, 1.0f);

    std::string val = HT_FormatShort(total);
    ImVec2 ts = ImGui::CalcTextSize(val.c_str());
    dl->AddText(ImVec2(c.x - ts.x * 0.5f, c.y - 14.0f), IM_COL32(235, 245, 255, 255), val.c_str());
    const char* label = "TOTAL";
    ts = ImGui::CalcTextSize(label);
    dl->AddText(ImVec2(c.x - ts.x * 0.5f, c.y + 5.0f), IM_COL32(150, 165, 190, 255), label);
    ImGui::Dummy(ImVec2(size, size));
}

static void HP_DrawDpsPage(float leftW, float rightW)
{
    uint64_t total = 0; int dur = 0; std::string mob;
    auto rows = HP_GetLiveDpsRows(total, mob, dur);
    uint64_t raidDps = dur > 0 ? total / (uint64_t)std::max(1, dur) : 0;

    std::string fightDateText = "Unknown";
    int selectedFightForHeader = g_fullUiDpsSelectedFight.load();
    if (selectedFightForHeader >= 0) {
        std::lock_guard<std::mutex> hk(g_completedDpsMutex);
        if (selectedFightForHeader < (int)g_completedDpsFights.size()) {
            const auto& hf = g_completedDpsFights[(size_t)selectedFightForHeader];
            fightDateText = HP_FormatDateTimeLong(hf.wallEnded > 0 ? hf.wallEnded : hf.wallStarted);
        }
    } else if (!mob.empty()) {
        fightDateText = "Live Fight";
    }
    int deathCountForHeader = (int)HP_GetSelectedDeaths().size();

    uint64_t typeMelee = 0, typeSpell = 0, typeDot = 0, typeProc = 0, typePet = 0, typeSwarm = 0, typeOther = 0;
    uint64_t maxHit = 0, totalHits = 0;
    for (const auto& r : rows) {
        typeMelee += r.melee; typeSpell += r.spell; typeDot += r.dot; typeProc += r.proc;
        typePet += r.pet; typeSwarm += r.swarm; typeOther += r.other;
        if (r.maxHit > maxHit) maxHit = r.maxHit;
        totalHits += r.hits;
    }

    const float fightsW = std::min(480.0f, std::max(410.0f, leftW * 0.34f));
    const float detailW = std::max(620.0f, leftW - fightsW - 10.0f);
    HP_DrawDpsFightList(fightsW);
    ImGui::SameLine();

    ImGui::BeginChild("##dps_main", ImVec2(detailW, 0), true);

    ImDrawList* dl = ImGui::GetWindowDrawList();
    ImVec2 headerPos = ImGui::GetCursorScreenPos();
    float headerW = ImGui::GetContentRegionAvail().x;
    dl->AddRectFilled(headerPos, ImVec2(headerPos.x + headerW, headerPos.y + 78.0f), IM_COL32(6, 12, 25, 215), 10.0f);
    dl->AddRect(headerPos, ImVec2(headerPos.x + headerW, headerPos.y + 78.0f), IM_COL32(52, 128, 245, 130), 10.0f, 0, 1.0f);
    // Mob header icon + title
    int headerMobRace = 0;
    int headerMobBody = 0;
    std::string headerMobIconKey;
    if (selectedFightForHeader >= 0) {
        std::lock_guard<std::mutex> hk(g_completedDpsMutex);
        if (selectedFightForHeader < (int)g_completedDpsFights.size()) {
            const auto& hf = g_completedDpsFights[(size_t)selectedFightForHeader];
            headerMobRace = hf.mobRace;
            headerMobBody = hf.mobBodyType;
            headerMobIconKey = hf.mobIconKey;
        }
    } else {
        std::lock_guard<std::mutex> lk(g_liveDpsMutex);
        headerMobRace = g_liveDps.mobRace;
        headerMobBody = g_liveDps.mobBodyType;
        headerMobIconKey = g_liveDps.mobIconKey;
    }
    HP_DrawMobIconInList(dl, ImVec2(headerPos.x + 16.0f, headerPos.y + 15.0f), 46.0f, headerMobRace, headerMobBody, headerMobIconKey, mob);
    ImGui::SetCursorScreenPos(ImVec2(headerPos.x + 74.0f, headerPos.y + 12.0f));
    ImGui::PushStyleColor(ImGuiCol_Text, IM_COL32(235, 245, 255, 255));
    ImGui::Text("%s", mob.c_str());
    ImGui::PopStyleColor();
    ImGui::SetCursorScreenPos(ImVec2(headerPos.x + 74.0f, headerPos.y + 43.0f));
    ImGui::TextDisabled("%s  •  Duration: %02d:%02d  •  Players: %d", fightDateText.c_str(), dur / 60, dur % 60, (int)rows.size());
    ImGui::SetCursorScreenPos(ImVec2(headerPos.x + headerW - 92.0f, headerPos.y + 14.0f));
    ImGui::Button("EXPORT", ImVec2(80.0f, 28.0f));
    ImGui::SetCursorScreenPos(ImVec2(headerPos.x, headerPos.y + 86.0f));

    HP_LoadPlayersIconTextureIfNeeded();
    HP_LoadDeathsIconTextureIfNeeded();
    HP_LoadDurationIconTextureIfNeeded();
    char durText[32]; std::snprintf(durText, sizeof(durText), "%02d:%02d", dur / 60, dur % 60);
    {
        ImVec2 cardsStart = ImGui::GetCursorScreenPos();
        float avail = ImGui::GetContentRegionAvail().x;
        const float gap = 8.0f;
        float cardW = std::max(84.0f, (avail - gap * 6.0f) / 7.0f);
        std::string meName;
        if (auto pChar = GetCharInfo()) { if (pChar->Name[0]) meName = pChar->Name; }
        uint64_t myDamage = 0;
        for (const auto& rr : rows) {
            if (!meName.empty() && (rr.name == meName || rr.name.find(meName) != std::string::npos)) { myDamage += rr.dmg; }
        }
        uint64_t myDps = dur > 0 ? myDamage / (uint64_t)std::max(1, dur) : 0;
        struct StatCardDef { const char* title; std::string value; const char* sub; ImU32 accent; } cards[7] = {
            { "TOTAL DAMAGE", HT_FormatShort(total), "", IM_COL32(55, 170, 255, 255) },
            { "RAID DPS", HT_FormatInteger(raidDps), "", IM_COL32(55, 170, 255, 255) },
            { "YOUR DPS", HT_FormatInteger(myDps), meName.empty() ? "" : meName.c_str(), IM_COL32(55, 170, 255, 255) },
            { "SWINGS", HT_FormatInteger(totalHits), "", IM_COL32(55, 170, 255, 255) },
            { "DURATION", durText, "", IM_COL32(55, 170, 255, 255) },
            { "PLAYERS", std::to_string((int)rows.size()), "", IM_COL32(55, 170, 255, 255) },
            { "DEATHS", std::to_string(deathCountForHeader), "", IM_COL32(255, 70, 70, 255) }
        };
        for (int ci = 0; ci < 7; ++ci) {
            ImGui::SetCursorScreenPos(ImVec2(cardsStart.x + (cardW + gap) * ci, cardsStart.y));
            HP_IconTexture* cardIcon = nullptr;
            if (std::strcmp(cards[ci].title, "PLAYERS") == 0) cardIcon = &g_playersIconTexture;
            else if (std::strcmp(cards[ci].title, "DEATHS") == 0) cardIcon = &g_deathsIconTexture;
            else if (std::strcmp(cards[ci].title, "DURATION") == 0) cardIcon = &g_durationIconTexture;
            HP_DrawDpsHeroStat(cards[ci].title, cards[ci].value.c_str(), cards[ci].sub, cards[ci].accent, cardW, cardIcon);
        }
        ImGui::SetCursorScreenPos(ImVec2(cardsStart.x, cardsStart.y + 74.0f));
    }

    ImGui::Spacing();
    float upperH = 200.0f;
    float graphW = std::max(320.0f, (ImGui::GetContentRegionAvail().x - 12.0f) * 0.58f);
    ImGui::BeginChild("##dps_graph_panel", ImVec2(graphW, upperH), true);
    ImGui::TextColored(ImVec4(0.32f, 0.72f, 1.0f, 1.0f), "DPS OVER TIME");
    HP_DrawDpsMiniGraph(rows, total, ImGui::GetContentRegionAvail().x, 154.0f, dur, "DPS");
    ImGui::EndChild();
    ImGui::SameLine();
    ImGui::BeginChild("##dps_donut_panel", ImVec2(0, upperH), true);
    ImGui::TextColored(ImVec4(0.62f, 0.45f, 1.0f, 1.0f), "DAMAGE TYPE BREAKDOWN");
    HP_DrawDpsDonutFallback(typeMelee, typeSpell, typeDot, typePet + typeSwarm + typeProc, typeOther, total, 118.0f);
    ImGui::SameLine();
    ImGui::BeginGroup();
    HP_DrawDpsTypeBar("Melee", typeMelee, total, IM_COL32(40,130,255,255), 110.0f);
    HP_DrawDpsTypeBar("Spell", typeSpell, total, IM_COL32(145,80,255,255), 110.0f);
    HP_DrawDpsTypeBar("DoT", typeDot, total, IM_COL32(255,115,30,255), 110.0f);
    HP_DrawDpsTypeBar("Pet", typePet + typeSwarm, total, IM_COL32(70,210,120,255), 110.0f);
    HP_DrawDpsTypeBar("Proc", typeProc, total, IM_COL32(255,190,60,255), 110.0f);
    ImGui::EndGroup();
    ImGui::EndChild();

    ImGui::Spacing();
    float playerPanelH = std::max(250.0f, ImGui::GetContentRegionAvail().y - 160.0f);
    ImGui::BeginChild("##dps_player_panel", ImVec2(0, playerPanelH), true);
    ImGui::TextColored(ImVec4(0.32f, 0.72f, 1.0f, 1.0f), "PLAYER DAMAGE");
    ImGui::SameLine(ImGui::GetContentRegionAvail().x - 250.0f);
    ImGui::TextDisabled(g_dpsCombinePets ? "COMBINE PETS" : "SPLIT PETS");
    ImGui::SameLine();
    HP_ToggleSwitch("##pet_combine_toggle", &g_dpsCombinePets);
    ImGui::SameLine();
    ImGui::Button("COPY", ImVec2(64.0f, 24.0f));

    if (ImGui::BeginTable("##dps_table_futuristic", 11,
        ImGuiTableFlags_RowBg | ImGuiTableFlags_BordersInnerH | ImGuiTableFlags_SizingStretchProp | ImGuiTableFlags_ScrollY,
        ImVec2(0, ImGui::GetContentRegionAvail().y))) {
        ImGui::TableSetupColumn("#", ImGuiTableColumnFlags_WidthFixed, 30);
        ImGui::TableSetupColumn("Player", ImGuiTableColumnFlags_WidthStretch, 1.55f);
        ImGui::TableSetupColumn("Class", ImGuiTableColumnFlags_WidthFixed, 68);
        ImGui::TableSetupColumn("Damage", ImGuiTableColumnFlags_WidthFixed, 152);
        ImGui::TableSetupColumn("DPS", ImGuiTableColumnFlags_WidthFixed, 82);
        ImGui::TableSetupColumn("%", ImGuiTableColumnFlags_WidthFixed, 50);
        ImGui::TableSetupColumn("Max", ImGuiTableColumnFlags_WidthFixed, 72);
        ImGui::TableSetupColumn("Hits", ImGuiTableColumnFlags_WidthFixed, 56);
        ImGui::TableSetupColumn("Melee", ImGuiTableColumnFlags_WidthFixed, 72);
        ImGui::TableSetupColumn("Spell", ImGuiTableColumnFlags_WidthFixed, 72);
        ImGui::TableSetupColumn("Types", ImGuiTableColumnFlags_WidthFixed, 122);
        ImGui::TableHeadersRow();

        int i = 0;
        for (auto& r : rows) {
            uint64_t dps = dur > 0 ? r.dmg / (uint64_t)std::max(1, dur) : 0;
            double pct = total > 0 ? (double)r.dmg * 100.0 / (double)total : 0.0;
            ImGui::TableNextRow(ImGuiTableRowFlags_None, 24.0f);
            ImGui::TableSetColumnIndex(0); ImGui::Text("%d", ++i);
            ImGui::TableSetColumnIndex(1);
            bool selected = (g_fullUiDpsSelectedPlayer == r.name);
            ImGui::PushStyleColor(ImGuiCol_Text, (r.name.find("Dorfus") != std::string::npos) ? IM_COL32(90, 230, 90, 255) : IM_COL32(75, 205, 255, 255));
            if (ImGui::Selectable(r.name.c_str(), selected, ImGuiSelectableFlags_SpanAllColumns))
                g_fullUiDpsSelectedPlayer = r.name;
            ImGui::PopStyleColor();
            ImGui::TableSetColumnIndex(2);
            {
                std::string cls = HP_GetPlayerClassName(r.name);
                HP_IconTexture* classIcon = HP_GetClassIconTexture(cls);

                if (classIcon && classIcon->id) {
                    ImVec2 cp = ImGui::GetCursorScreenPos();
                    ImGui::GetWindowDrawList()->AddImage(classIcon->id, cp, ImVec2(cp.x + 22.0f, cp.y + 22.0f));
                    ImGui::SetCursorScreenPos(ImVec2(cp.x + 26.0f, cp.y + 2.0f));
                }
                ImGui::TextDisabled("%s", cls.c_str());
            }
            ImGui::TableSetColumnIndex(3);
            float cellW = ImGui::GetContentRegionAvail().x;
            ImVec2 p = ImGui::GetCursorScreenPos();
            float frac = total > 0 ? (float)((double)r.dmg / (double)total) : 0.0f;
            ImGui::GetWindowDrawList()->AddRectFilled(ImVec2(p.x + 58.0f, p.y + 3.0f), ImVec2(p.x + 58.0f + (cellW - 66.0f) * frac, p.y + 17.0f), IM_COL32(32, 112, 235, 210), 2.0f);
            ImGui::Text("%s", HT_FormatShort(r.dmg).c_str());
            ImGui::TableSetColumnIndex(4); ImGui::Text("%s", HT_FormatInteger(dps).c_str());
            ImGui::TableSetColumnIndex(5); ImGui::Text("%.1f", pct);
            ImGui::TableSetColumnIndex(6); ImGui::Text("%u", r.maxHit);
            ImGui::TableSetColumnIndex(7); ImGui::Text("%u", r.hits);
            ImGui::TableSetColumnIndex(8); ImGui::Text("%s", HT_FormatShort(r.melee).c_str());
            ImGui::TableSetColumnIndex(9); ImGui::Text("%s", HT_FormatShort(r.spell).c_str());
            ImGui::TableSetColumnIndex(10);
            HP_DrawDpsTypeStackBar(r, std::min(104.0f, ImGui::GetContentRegionAvail().x - 4.0f), 10.0f);
        }
        if (total > 0) {
            ImGui::TableNextRow();
            ImGui::TableSetColumnIndex(1); ImGui::TextDisabled("TOTAL");
            ImGui::TableSetColumnIndex(3); ImGui::TextDisabled("%s", HT_FormatShort(total).c_str());
            ImGui::TableSetColumnIndex(4); ImGui::TextDisabled("%s", HT_FormatInteger(raidDps).c_str());
            ImGui::TableSetColumnIndex(5); ImGui::TextDisabled("100%%");
            ImGui::TableSetColumnIndex(6); ImGui::TextDisabled("%s", HT_FormatInteger(maxHit).c_str());
            ImGui::TableSetColumnIndex(7); ImGui::TextDisabled("%s", HT_FormatInteger(totalHits).c_str());
        }
        ImGui::EndTable();
    }
    ImGui::EndChild();

    ImGui::Spacing();
    float bottomW = ImGui::GetContentRegionAvail().x;
    float panelGap = 8.0f;
    float panelW = std::max(160.0f, (bottomW - panelGap * 2.0f) / 3.0f);

    {
        ImVec2 dp0 = ImGui::GetCursorScreenPos();
        ImGui::PushStyleColor(ImGuiCol_ChildBg, IM_COL32(8, 8, 22, 235));
        ImGui::PushStyleColor(ImGuiCol_Border, IM_COL32(150, 70, 220, 190));
        ImGui::BeginChild("##dps_deaths_panel", ImVec2(panelW, 158.0f), true);
        HP_LoadDeathsIconTextureIfNeeded();
        HP_DrawPanelTitleIconText(g_deathsIconTexture, "DEATHS (10)", ImVec4(0.82f, 0.45f, 1.0f, 1.0f));
        ImGui::Separator();
        auto deaths = HP_GetSelectedDeaths();
        if (deaths.empty()) {
            ImGui::TextDisabled("No PC deaths recorded for this fight.");
        } else if (ImGui::BeginTable("##dps_deaths_table", 4, ImGuiTableFlags_RowBg | ImGuiTableFlags_BordersInnerH | ImGuiTableFlags_SizingStretchProp, ImVec2(0, 88.0f))) {
            ImGui::TableSetupColumn("TIME", ImGuiTableColumnFlags_WidthFixed, 54.0f);
            ImGui::TableSetupColumn("PLAYER", ImGuiTableColumnFlags_WidthStretch, 1.0f);
            ImGui::TableSetupColumn("KILLER", ImGuiTableColumnFlags_WidthStretch, 1.25f);
            ImGui::TableSetupColumn("TOTAL DMG", ImGuiTableColumnFlags_WidthFixed, 86.0f);
            ImGui::TableHeadersRow();
            int dc = 0;
            for (const auto& d : deaths) {
                if (++dc > 10) break;
                int rel = 0;
                int sel = g_fullUiDpsSelectedFight.load();
                if (sel >= 0) {
                    std::lock_guard<std::mutex> hk(g_completedDpsMutex);
                    if (sel < (int)g_completedDpsFights.size() && g_completedDpsFights[(size_t)sel].startedMs > 0)
                        rel = (int)std::max<int64_t>(0, (d.ms - g_completedDpsFights[(size_t)sel].startedMs) / 1000);
                }
                char tbuf[16]; std::snprintf(tbuf, sizeof(tbuf), "%02d:%02d", rel / 60, rel % 60);
                ImGui::TableNextRow();
                ImGui::TableSetColumnIndex(0); ImGui::TextUnformatted(tbuf);
                ImGui::TableSetColumnIndex(1); ImGui::TextColored(ImVec4(0.35f, 0.82f, 1.0f, 1.0f), "%s", d.player.c_str());
                ImGui::TableSetColumnIndex(2); ImGui::TextColored(ImVec4(1.0f, 0.32f, 0.25f, 1.0f), "%s", d.killer.c_str());
                ImGui::TableSetColumnIndex(3); ImGui::Text("%s", HT_FormatInteger(d.recentDamage).c_str());
            }
            ImGui::EndTable();
        }
        if (!deaths.empty()) {
        ImGui::PushStyleColor(ImGuiCol_Text, ImVec4(0.20f, 1.00f, 0.20f, 1.0f));
        if (ImGui::Selectable("VIEW ALL DEATHS »", false, ImGuiSelectableFlags_SpanAllColumns)) ImGui::OpenPopup("All Deaths##popup");
        ImGui::PopStyleColor();
    }
        if (ImGui::BeginPopupModal("All Deaths##popup", nullptr, ImGuiWindowFlags_AlwaysAutoResize)) {
            ImGui::TextColored(ImVec4(0.82f, 0.45f, 1.0f, 1.0f), "All deaths for selected fight");
            ImGui::Separator();
            if (ImGui::BeginTable("##all_deaths_popup_table", 5, ImGuiTableFlags_RowBg | ImGuiTableFlags_BordersInnerH | ImGuiTableFlags_SizingStretchProp | ImGuiTableFlags_ScrollY, ImVec2(620.0f, 320.0f))) {
                ImGui::TableSetupColumn("Time", ImGuiTableColumnFlags_WidthFixed, 70.0f);
                ImGui::TableSetupColumn("Player", ImGuiTableColumnFlags_WidthStretch, 1.0f);
                ImGui::TableSetupColumn("Killer", ImGuiTableColumnFlags_WidthStretch, 1.0f);
                ImGui::TableSetupColumn("Spike Before Death", ImGuiTableColumnFlags_WidthFixed, 130.0f);
                ImGui::TableSetupColumn("Heals In Window", ImGuiTableColumnFlags_WidthFixed, 120.0f);
                ImGui::TableHeadersRow();
                for (const auto& d : deaths) {
                    int rel = 0;
                    int sel = g_fullUiDpsSelectedFight.load();
                    if (sel >= 0) { std::lock_guard<std::mutex> hk(g_completedDpsMutex); if (sel < (int)g_completedDpsFights.size() && g_completedDpsFights[(size_t)sel].startedMs > 0) rel = (int)std::max<int64_t>(0, (d.ms - g_completedDpsFights[(size_t)sel].startedMs) / 1000); }
                    char tbuf[16]; std::snprintf(tbuf, sizeof(tbuf), "%02d:%02d", rel / 60, rel % 60);
                    ImGui::TableNextRow();
                    ImGui::TableSetColumnIndex(0); ImGui::TextUnformatted(tbuf);
                    ImGui::TableSetColumnIndex(1); ImGui::TextColored(ImVec4(0.35f, 0.82f, 1.0f, 1.0f), "%s", d.player.c_str());
                    ImGui::TableSetColumnIndex(2); ImGui::TextColored(ImVec4(1.0f, 0.32f, 0.25f, 1.0f), "%s", d.killer.c_str());
                    ImGui::TableSetColumnIndex(3); ImGui::Text("%s", HT_FormatInteger(d.recentDamage).c_str());
                    ImGui::TableSetColumnIndex(4); ImGui::TextDisabled("tracked soon");
                }
                ImGui::EndTable();
            }
            if (ImGui::Button("Close", ImVec2(100, 28))) ImGui::CloseCurrentPopup();
            ImGui::EndPopup();
        }
        ImGui::EndChild();
        ImGui::PopStyleColor(2);
        ImVec2 dp1 = ImGui::GetItemRectMax();
        ImGui::GetWindowDrawList()->AddRect(dp0, dp1, IM_COL32(160, 75, 235, 170), 10.0f, 0, 1.2f);
    }

    ImGui::SameLine();
    ImGui::PushStyleColor(ImGuiCol_ChildBg, IM_COL32(8, 8, 22, 235));
    ImGui::PushStyleColor(ImGuiCol_Border, IM_COL32(150, 70, 220, 190));
    ImGui::BeginChild("##dps_spikes_panel", ImVec2(panelW, 158.0f), true);
    HP_LoadDpsIconTextureIfNeeded();
    HP_DrawPanelTitleIconText(g_dpsIconTexture, "MAX DPS SPIKE", ImVec4(0.82f, 0.45f, 1.0f, 1.0f));
    ImGui::Separator();
    struct SpikeRow { std::string name; uint64_t spike; std::string time; std::string type; std::string target; int64_t wall = 0; };
    struct RaidDpsSpikeRow {
        uint64_t total = 0;
        int64_t startWall = 0;
        int64_t endWall = 0;
        std::string time;
        std::vector<HP_DpsSpikeEvent> hits;
    };
    std::vector<SpikeRow> spikes;
    std::vector<RaidDpsSpikeRow> raidSpikeRows;
    uint64_t raidSpikeTotal = 0;
    std::string spikeTime = "--:--:--";
    std::vector<HP_DpsSpikeEvent> dpsSpikeEvents;
    {
        int sel = g_fullUiDpsSelectedFight.load();
        if (!g_dpsSelectedFights.empty()) {
            static std::string s_cachedSpikeKey;
            static std::vector<HP_DpsSpikeEvent> s_cachedSpikeEvents;
            std::string key = HP_BuildSelectedFightCacheKey();
            if (key == s_cachedSpikeKey) {
                dpsSpikeEvents = s_cachedSpikeEvents;
            } else {
                std::lock_guard<std::mutex> hk(g_completedDpsMutex);
                for (int idx : g_dpsSelectedFights) {
                    if (idx >= 0 && idx < (int)g_completedDpsFights.size()) {
                        const auto& src = g_completedDpsFights[(size_t)idx].dpsSpikes;
                        size_t room = dpsSpikeEvents.size() < 5000 ? (5000 - dpsSpikeEvents.size()) : 0;
                        if (room == 0) break;
                        if (src.size() <= room) dpsSpikeEvents.insert(dpsSpikeEvents.end(), src.begin(), src.end());
                        else dpsSpikeEvents.insert(dpsSpikeEvents.end(), src.begin(), src.begin() + room);
                    }
                }
                s_cachedSpikeKey = key;
                s_cachedSpikeEvents = dpsSpikeEvents;
            }
        } else if (sel >= 0) {
            std::lock_guard<std::mutex> hk(g_completedDpsMutex);
            if (sel < (int)g_completedDpsFights.size()) dpsSpikeEvents = g_completedDpsFights[(size_t)sel].dpsSpikes;
        } else {
            std::lock_guard<std::mutex> lk(g_liveDpsMutex);
            dpsSpikeEvents = g_liveDps.dpsSpikes;
        }
    }
    std::unordered_map<int64_t, size_t> raidSpikeIndexByWindow;
    for (const auto& ev : dpsSpikeEvents) {
        if (ev.amount == 0) continue;
        spikes.push_back({ ev.player, ev.amount, HP_FormatTimeWithSeconds(ev.wall), ev.type, ev.target, ev.wall });
        int64_t wall = ev.wall > 0 ? ev.wall : HP_WallNow();
        int64_t bucket = wall / 5; // 5-second raid/group DPS spike window
        auto itBucket = raidSpikeIndexByWindow.find(bucket);
        if (itBucket == raidSpikeIndexByWindow.end()) {
            RaidDpsSpikeRow row;
            row.startWall = bucket * 5;
            row.endWall = row.startWall + 5;
            row.time = HP_FormatTimeWithSeconds(wall);
            raidSpikeIndexByWindow[bucket] = raidSpikeRows.size();
            raidSpikeRows.push_back(std::move(row));
            itBucket = raidSpikeIndexByWindow.find(bucket);
        }
        auto& row = raidSpikeRows[itBucket->second];
        row.total += ev.amount;
        row.hits.push_back(ev);
        if (wall > row.startWall) row.time = HP_FormatTimeWithSeconds(wall);
    }
    std::sort(spikes.begin(), spikes.end(), [](const SpikeRow& a, const SpikeRow& b){ return a.spike > b.spike; });
    std::sort(raidSpikeRows.begin(), raidSpikeRows.end(), [](const RaidDpsSpikeRow& a, const RaidDpsSpikeRow& b){
        return a.startWall > b.startWall;
    });
    for (const auto& row : raidSpikeRows) {
        if (row.total > raidSpikeTotal) {
            raidSpikeTotal = row.total;
            spikeTime = row.time;
        }
    }
    if (raidSpikeTotal > 0) {
        ImGui::Text("Max Raid/Group DPS spike");
        ImGui::TextColored(ImVec4(0.35f,0.82f,1.0f,1.0f), "%s", HT_FormatInteger(raidSpikeTotal).c_str());
        ImGui::SameLine(); ImGui::TextDisabled("at %s", spikeTime.c_str());
    } else {
        ImGui::TextDisabled("No raid/group DPS spike data for this fight yet.");
    }
    static RaidDpsSpikeRow selectedAllDpsSpikeDetail;
    static bool selectedAllDpsSpikeValid = false;
    if (!raidSpikeRows.empty()) {
        ImGui::PushStyleColor(ImGuiCol_Text, ImVec4(0.20f, 1.00f, 0.20f, 1.0f));
        if (ImGui::Selectable("VIEW ALL DPS SPIKES »", false, ImGuiSelectableFlags_SpanAllColumns)) ImGui::OpenPopup("All DPS Spikes##popup");
        ImGui::PopStyleColor();
    }
    if (ImGui::BeginPopupModal("All DPS Spikes##popup", nullptr, ImGuiWindowFlags_AlwaysAutoResize)) {
        ImGui::TextColored(ImVec4(0.82f, 0.45f, 1.0f, 1.0f), "Raid/Group DPS spikes during selected fight");
        ImGui::TextDisabled("Click a spike to see every hit in that 5-second window.");
        ImGui::Separator();
        if (ImGui::BeginTable("##all_dps_spikes_popup_table", 4, ImGuiTableFlags_RowBg | ImGuiTableFlags_BordersInnerH | ImGuiTableFlags_SizingStretchProp | ImGuiTableFlags_ScrollY, ImVec2(620.0f, 320.0f))) {
            ImGui::TableSetupColumn("#", ImGuiTableColumnFlags_WidthFixed, 34.0f);
            ImGui::TableSetupColumn("Time", ImGuiTableColumnFlags_WidthFixed, 120.0f);
            ImGui::TableSetupColumn("Raid/Group Spike", ImGuiTableColumnFlags_WidthFixed, 150.0f);
            ImGui::TableSetupColumn("Hits", ImGuiTableColumnFlags_WidthFixed, 80.0f);
            ImGui::TableHeadersRow();
            int n = 0;
            for (const auto& s : raidSpikeRows) {
                ImGui::TableNextRow();
                ImGui::TableSetColumnIndex(0); ImGui::Text("%d", ++n);
                ImGui::TableSetColumnIndex(1);
                std::string label = s.time + "##all_raid_dps_spike_" + std::to_string(n);
                if (ImGui::Selectable(label.c_str(), false, ImGuiSelectableFlags_SpanAllColumns)) {
                    selectedAllDpsSpikeDetail = s;
                    selectedAllDpsSpikeValid = true;
                    ImGui::OpenPopup("Raid DPS Spike Detail##all_spikes");
                }
                ImGui::TableSetColumnIndex(2); ImGui::TextColored(ImVec4(0.35f,0.82f,1.0f,1.0f), "%s", HT_FormatInteger(s.total).c_str());
                ImGui::TableSetColumnIndex(3); ImGui::Text("%d", (int)s.hits.size());
            }
            ImGui::EndTable();
        }
        if (ImGui::BeginPopupModal("Raid DPS Spike Detail##all_spikes", nullptr, ImGuiWindowFlags_AlwaysAutoResize)) {
            if (selectedAllDpsSpikeValid) {
                ImGui::TextColored(ImVec4(0.35f,0.82f,1.0f,1.0f), "Raid/Group DPS Spike Detail");
                ImGui::Separator();
                ImGui::Text("Window: %s - %s", HP_FormatTimeWithSeconds(selectedAllDpsSpikeDetail.startWall).c_str(), HP_FormatTimeWithSeconds(selectedAllDpsSpikeDetail.endWall).c_str());
                ImGui::Text("Total Damage: %s", HT_FormatInteger(selectedAllDpsSpikeDetail.total).c_str());
                if (ImGui::BeginTable("##all_dps_spike_detail_hits", 5, ImGuiTableFlags_RowBg | ImGuiTableFlags_BordersInnerH | ImGuiTableFlags_SizingStretchProp | ImGuiTableFlags_ScrollY, ImVec2(680.0f, 280.0f))) {
                    ImGui::TableSetupColumn("Time", ImGuiTableColumnFlags_WidthFixed, 120.0f);
                    ImGui::TableSetupColumn("Player", ImGuiTableColumnFlags_WidthStretch, 1.0f);
                    ImGui::TableSetupColumn("Target", ImGuiTableColumnFlags_WidthStretch, 1.0f);
                    ImGui::TableSetupColumn("Type", ImGuiTableColumnFlags_WidthFixed, 80.0f);
                    ImGui::TableSetupColumn("Damage", ImGuiTableColumnFlags_WidthFixed, 100.0f);
                    ImGui::TableHeadersRow();
                    for (const auto& hit : selectedAllDpsSpikeDetail.hits) {
                        ImGui::TableNextRow();
                        ImGui::TableSetColumnIndex(0); ImGui::TextDisabled("%s", HP_FormatTimeWithSeconds(hit.wall).c_str());
                        ImGui::TableSetColumnIndex(1); ImGui::TextColored(ImVec4(0.35f,0.82f,1.0f,1.0f), "%s", hit.player.c_str());
                        ImGui::TableSetColumnIndex(2); ImGui::TextUnformatted(hit.target.c_str());
                        ImGui::TableSetColumnIndex(3); ImGui::TextDisabled("%s", hit.type.c_str());
                        ImGui::TableSetColumnIndex(4); ImGui::Text("%s", HT_FormatInteger(hit.amount).c_str());
                    }
                    ImGui::EndTable();
                }
            }
            if (ImGui::Button("Close", ImVec2(100, 28))) ImGui::CloseCurrentPopup();
            ImGui::EndPopup();
        }
        if (ImGui::Button("Close", ImVec2(100, 28))) ImGui::CloseCurrentPopup();
        ImGui::EndPopup();
    }
    ImGui::EndChild();
    ImGui::PopStyleColor(2);

    ImGui::SameLine();
    ImGui::PushStyleColor(ImGuiCol_ChildBg, IM_COL32(8, 8, 22, 235));
    ImGui::PushStyleColor(ImGuiCol_Border, IM_COL32(150, 70, 220, 190));
    ImGui::BeginChild("##dps_summary_panel", ImVec2(0, 168.0f), true);
    HP_LoadHistoryIconTextureIfNeeded();
    HP_DrawPanelTitleIconText(g_historyIconTexture, "FIGHT SUMMARY", ImVec4(0.78f, 0.42f, 1.0f, 1.0f));
    ImGui::Separator();
    std::string firstHitText = "--:--:--";
    std::string lastHitText = "--:--:--";
    {
        int sel = g_fullUiDpsSelectedFight.load();
        if (sel >= 0) {
            std::lock_guard<std::mutex> hk(g_completedDpsMutex);
            if (sel < (int)g_completedDpsFights.size()) {
                const auto& sf = g_completedDpsFights[(size_t)sel];
                firstHitText = HP_FormatTimeWithSeconds(sf.wallStarted);
                lastHitText = HP_FormatTimeWithSeconds(sf.wallEnded);
            }
        } else {
            std::lock_guard<std::mutex> lk(g_liveDpsMutex);
            firstHitText = HP_FormatTimeWithSeconds(g_liveDps.wallStarted);
            lastHitText = HP_FormatTimeWithSeconds(HP_WallNow());
        }
    }
    std::string durSecsText = std::to_string(std::max(0, dur)) + "s";
    std::string meName2;
    if (auto pChar = GetCharInfo()) { if (pChar->Name[0]) meName2 = pChar->Name; }
    uint64_t myDamage2 = 0;
    for (const auto& rr : rows) if (!meName2.empty() && (rr.name == meName2 || rr.name.find(meName2) != std::string::npos)) myDamage2 += rr.dmg;
    uint64_t myDps2 = dur > 0 ? myDamage2 / (uint64_t)std::max(1, dur) : 0;
    ImGui::SetWindowFontScale(0.90f);
    if (ImGui::BeginTable("##fight_summary_fit", 4, ImGuiTableFlags_SizingFixedFit | ImGuiTableFlags_NoHostExtendX)) {
        ImGui::TableSetupColumn("##l1", ImGuiTableColumnFlags_WidthFixed, 66.0f);
        ImGui::TableSetupColumn("##v1", ImGuiTableColumnFlags_WidthFixed, 82.0f);
        ImGui::TableSetupColumn("##l2", ImGuiTableColumnFlags_WidthFixed, 76.0f);
        ImGui::TableSetupColumn("##v2", ImGuiTableColumnFlags_WidthFixed, 74.0f);
#define HP_SUMMARY_ROW(a,b,c,d)         ImGui::TableNextRow();         ImGui::TableSetColumnIndex(0); ImGui::TextUnformatted(a);         ImGui::TableSetColumnIndex(1); ImGui::TextUnformatted(b.c_str());         ImGui::TableSetColumnIndex(2); ImGui::TextUnformatted(c);         ImGui::TableSetColumnIndex(3); ImGui::TextUnformatted(d.c_str())
        HP_SUMMARY_ROW("First Hit:", firstHitText, "Total Dmg:", HT_FormatShort(total));
        HP_SUMMARY_ROW("Last Hit:", lastHitText, "Raid DPS:", HT_FormatInteger(raidDps));
        HP_SUMMARY_ROW("Duration:", durSecsText, "Your DPS:", HT_FormatInteger(myDps2));
        HP_SUMMARY_ROW("Players:", std::to_string((int)rows.size()), "Swings:", HT_FormatInteger(totalHits));
        HP_SUMMARY_ROW("Deaths:", std::to_string(deathCountForHeader), "Max Hit:", HT_FormatInteger(maxHit));
#undef HP_SUMMARY_ROW
        ImGui::EndTable();
    }

    ImGui::PushStyleColor(ImGuiCol_Text, ImVec4(0.20f, 1.00f, 0.20f, 1.0f));
    if (ImGui::Selectable("VIEW ALL FIGHT SUMMARY »", false, ImGuiSelectableFlags_SpanAllColumns)) ImGui::OpenPopup("Fight Logs##popup");
    ImGui::PopStyleColor();
    if (ImGui::BeginPopupModal("Fight Logs##popup", nullptr, ImGuiWindowFlags_AlwaysAutoResize)) {
        static char fightLogSearch[128] = "";
        ImGui::TextColored(ImVec4(0.78f, 0.42f, 1.0f, 1.0f), "Fight logs for selected encounter");
        ImGui::SetNextItemWidth(520.0f);
        ImGui::InputText("Search", fightLogSearch, sizeof(fightLogSearch));
        std::vector<std::string> fightLogs;
        int sel = g_fullUiDpsSelectedFight.load();
        if (sel >= 0) {
            std::lock_guard<std::mutex> hk(g_completedDpsMutex);
            if (sel < (int)g_completedDpsFights.size()) fightLogs = g_completedDpsFights[(size_t)sel].logs;
        } else {
            std::lock_guard<std::mutex> lk(g_liveDpsMutex);
            fightLogs = g_liveDps.logs;
        }
        std::string needle = LowerCopy(fightLogSearch);
        // Keep the fight-log popup scrollbar at the same large style used globally.
        ImGui::PushStyleVar(ImGuiStyleVar_ScrollbarSize, 18.0f);
        ImGui::PushStyleVar(ImGuiStyleVar_ScrollbarRounding, 18.0f);
        ImGui::PushStyleColor(ImGuiCol_ScrollbarBg, IM_COL32(10, 8, 24, 120));
        ImGui::PushStyleColor(ImGuiCol_ScrollbarGrab, IM_COL32(150, 80, 255, 230));
        ImGui::PushStyleColor(ImGuiCol_ScrollbarGrabHovered, IM_COL32(185, 110, 255, 245));
        ImGui::PushStyleColor(ImGuiCol_ScrollbarGrabActive, IM_COL32(215, 150, 255, 255));
        if (ImGui::BeginChild("##fight_log_popup_scroll", ImVec2(760.0f, 420.0f), true, ImGuiWindowFlags_AlwaysVerticalScrollbar)) {
            int shownLogs = 0;
            for (const auto& lineText : fightLogs) {
                if (!needle.empty() && LowerCopy(lineText).find(needle) == std::string::npos) continue;
                ImGui::TextWrapped("%s", lineText.c_str());
                ++shownLogs;
            }
            if (shownLogs == 0) ImGui::TextDisabled("No matching fight logs saved for this encounter.");
        }
        ImGui::EndChild();
        ImGui::PopStyleColor(4);
        ImGui::PopStyleVar(2);
        if (ImGui::Button("Close", ImVec2(100, 28))) ImGui::CloseCurrentPopup();
        ImGui::EndPopup();
    }
    ImGui::SetWindowFontScale(1.0f);
    ImGui::EndChild();
    ImGui::PopStyleColor(2);

    ImGui::EndChild();

    ImGui::SameLine();
    ImGui::BeginChild("##dps_side", ImVec2(rightW, 0), false);

    const HP_DpsUiRow* selectedRow = nullptr;
    for (const auto& r : rows) {
        if (r.name == g_fullUiDpsSelectedPlayer) { selectedRow = &r; break; }
    }
    if (!selectedRow && !rows.empty()) selectedRow = &rows.front();

    ImGui::PushStyleColor(ImGuiCol_ChildBg, IM_COL32(7, 10, 24, 235));
    ImGui::PushStyleColor(ImGuiCol_Border, IM_COL32(120, 70, 220, 185));
    ImGui::BeginChild("##right_top_spells_box", ImVec2(0, 270.0f), true);
    ImGui::TextColored(ImVec4(0.32f, 0.72f, 1.0f, 1.0f), "TOP SPELLS");
    ImGui::Separator();
    struct HP_TopSpellUiRow { std::string spell; uint32_t casts = 0; uint64_t damage = 0; };
    std::vector<HP_TopSpellUiRow> topSpellRows;
    {
        auto fightSpells = HP_GetSelectedDpsSpellCasts();
        for (const auto& kv : fightSpells) {
            if (!kv.first.empty() && kv.second > 0)
                topSpellRows.push_back({ kv.first, kv.second, 0 });
        }
    }
    std::sort(topSpellRows.begin(), topSpellRows.end(), [](const HP_TopSpellUiRow& a, const HP_TopSpellUiRow& b) {
        if (a.casts != b.casts) return a.casts > b.casts;
        return a.spell < b.spell;
    });
    if (ImGui::BeginTable("##top_spells_actual", 4, ImGuiTableFlags_RowBg | ImGuiTableFlags_BordersInnerH | ImGuiTableFlags_SizingStretchProp | ImGuiTableFlags_ScrollY, ImVec2(0, ImGui::GetContentRegionAvail().y - 24.0f))) {
        ImGui::TableSetupColumn("SPELL / BURN", ImGuiTableColumnFlags_WidthStretch, 1.7f);
        ImGui::TableSetupColumn("CASTS", ImGuiTableColumnFlags_WidthFixed, 50.0f);
        ImGui::TableSetupColumn("DAMAGE", ImGuiTableColumnFlags_WidthFixed, 72.0f);
        ImGui::TableSetupColumn("%", ImGuiTableColumnFlags_WidthFixed, 40.0f);
        ImGui::TableHeadersRow();
        int shown = 0;
        for (const auto& r : topSpellRows) {
            if (++shown > 8) break;
            ImGui::TableNextRow();
            ImGui::TableSetColumnIndex(0); ImGui::TextColored(ImVec4(0.35f,0.82f,1.0f,1.0f), "%s", r.spell.c_str());
            ImGui::TableSetColumnIndex(1); ImGui::Text("%u", r.casts);
            ImGui::TableSetColumnIndex(2); ImGui::TextDisabled("--");
            ImGui::TableSetColumnIndex(3); ImGui::TextDisabled("--");
        }
        if (shown == 0) { ImGui::TableNextRow(); ImGui::TableSetColumnIndex(0); ImGui::TextDisabled("No spell casts detected yet."); }
        ImGui::EndTable();
    }
    ImGui::PushStyleColor(ImGuiCol_Text, ImVec4(0.20f, 1.00f, 0.20f, 1.0f));
    if (ImGui::Selectable("VIEW ALL SPELLS »", false, ImGuiSelectableFlags_SpanAllColumns)) ImGui::OpenPopup("All DPS Spells##popup");
    ImGui::PopStyleColor();
    if (ImGui::BeginPopupModal("All DPS Spells##popup", nullptr, ImGuiWindowFlags_AlwaysAutoResize)) {
        ImGui::TextColored(ImVec4(0.32f, 0.72f, 1.0f, 1.0f), "All spells and burns cast during selected fight");
        ImGui::TextDisabled("Shows every PC that cast a spell/burn during this fight and each spell count.");
        ImGui::Separator();

        struct HP_CasterSpellUiRow { std::string caster; std::string spell; uint32_t casts = 0; };
        std::vector<HP_CasterSpellUiRow> casterSpellRows;
        {
            auto byCaster = HP_GetSelectedDpsSpellCastsByCaster();
            for (const auto& ckv : byCaster) {
                for (const auto& skv : ckv.second) {
                    if (!ckv.first.empty() && !skv.first.empty() && skv.second > 0)
                        casterSpellRows.push_back({ ckv.first, skv.first, skv.second });
                }
            }
        }
        std::sort(casterSpellRows.begin(), casterSpellRows.end(), [](const HP_CasterSpellUiRow& a, const HP_CasterSpellUiRow& b) {
            if (a.caster != b.caster) return a.caster < b.caster;
            if (a.casts != b.casts) return a.casts > b.casts;
            return a.spell < b.spell;
        });

        std::vector<std::string> casterNames;
        {
            auto byCaster = HP_GetSelectedDpsSpellCastsByCaster();
            for (const auto& ckv : byCaster) {
                if (!ckv.first.empty()) casterNames.push_back(ckv.first);
            }
            std::sort(casterNames.begin(), casterNames.end());
        }

        static int s_compareCasterA = 0;
        static int s_compareCasterB = 1;
        if (!casterNames.empty()) {
            if (s_compareCasterA >= (int)casterNames.size()) s_compareCasterA = 0;
            if (s_compareCasterB >= (int)casterNames.size()) s_compareCasterB = casterNames.size() > 1 ? 1 : 0;

            ImGui::TextColored(ImVec4(0.95f, 0.55f, 1.0f, 1.0f), "Compare two PCs");
            ImGui::SetNextItemWidth(220.0f);
            if (ImGui::BeginCombo("PC A##spell_compare_a", casterNames[s_compareCasterA].c_str())) {
                for (int i = 0; i < (int)casterNames.size(); ++i) {
                    bool sel = (i == s_compareCasterA);
                    if (ImGui::Selectable(casterNames[i].c_str(), sel)) s_compareCasterA = i;
                    if (sel) ImGui::SetItemDefaultFocus();
                }
                ImGui::EndCombo();
            }
            ImGui::SameLine();
            ImGui::SetNextItemWidth(220.0f);
            if (ImGui::BeginCombo("PC B##spell_compare_b", casterNames[s_compareCasterB].c_str())) {
                for (int i = 0; i < (int)casterNames.size(); ++i) {
                    bool sel = (i == s_compareCasterB);
                    if (ImGui::Selectable(casterNames[i].c_str(), sel)) s_compareCasterB = i;
                    if (sel) ImGui::SetItemDefaultFocus();
                }
                ImGui::EndCombo();
            }

            auto byCaster = HP_GetSelectedDpsSpellCastsByCaster();
            const std::string aName = casterNames[s_compareCasterA];
            const std::string bName = casterNames[s_compareCasterB];
            std::unordered_map<std::string, uint32_t> aMap;
            std::unordered_map<std::string, uint32_t> bMap;
            auto ia = byCaster.find(aName); if (ia != byCaster.end()) aMap = ia->second;
            auto ib = byCaster.find(bName); if (ib != byCaster.end()) bMap = ib->second;

            std::vector<std::string> compareSpells;
            for (const auto& kv : aMap) if (!kv.first.empty()) compareSpells.push_back(kv.first);
            for (const auto& kv : bMap) if (!kv.first.empty() && std::find(compareSpells.begin(), compareSpells.end(), kv.first) == compareSpells.end()) compareSpells.push_back(kv.first);
            std::sort(compareSpells.begin(), compareSpells.end(), [&](const std::string& x, const std::string& y) {
                uint32_t xt = aMap[x] + bMap[x];
                uint32_t yt = aMap[y] + bMap[y];
                if (xt != yt) return xt > yt;
                return x < y;
            });

            if (ImGui::BeginTable("##spell_compare_table", 4, ImGuiTableFlags_RowBg | ImGuiTableFlags_BordersInnerH | ImGuiTableFlags_SizingStretchProp | ImGuiTableFlags_ScrollY, ImVec2(720.0f, 180.0f))) {
                ImGui::TableSetupColumn("Spell / Burn", ImGuiTableColumnFlags_WidthStretch, 1.4f);
                ImGui::TableSetupColumn(aName.c_str(), ImGuiTableColumnFlags_WidthFixed, 115.0f);
                ImGui::TableSetupColumn(bName.c_str(), ImGuiTableColumnFlags_WidthFixed, 115.0f);
                ImGui::TableSetupColumn("Total", ImGuiTableColumnFlags_WidthFixed, 80.0f);
                ImGui::TableHeadersRow();
                for (const std::string& spell : compareSpells) {
                    ImGui::TableNextRow();
                    ImGui::TableSetColumnIndex(0); ImGui::TextColored(ImVec4(0.35f,0.82f,1.0f,1.0f), "%s", spell.c_str());
                    ImGui::TableSetColumnIndex(1); ImGui::Text("%u", aMap[spell]);
                    ImGui::TableSetColumnIndex(2); ImGui::Text("%u", bMap[spell]);
                    ImGui::TableSetColumnIndex(3); ImGui::Text("%u", aMap[spell] + bMap[spell]);
                }
                if (compareSpells.empty()) {
                    ImGui::TableNextRow();
                    ImGui::TableSetColumnIndex(0);
                    ImGui::TextDisabled("No spell casts to compare.");
                }
                ImGui::EndTable();
            }
            ImGui::Separator();
        }

        if (ImGui::BeginTable("##all_dps_spells_popup_table", 4, ImGuiTableFlags_RowBg | ImGuiTableFlags_BordersInnerH | ImGuiTableFlags_SizingStretchProp | ImGuiTableFlags_ScrollY, ImVec2(720.0f, 320.0f))) {
            ImGui::TableSetupColumn("#", ImGuiTableColumnFlags_WidthFixed, 34.0f);
            ImGui::TableSetupColumn("NAME", ImGuiTableColumnFlags_WidthFixed, 150.0f);
            ImGui::TableSetupColumn("Spell / Burn", ImGuiTableColumnFlags_WidthStretch, 1.0f);
            ImGui::TableSetupColumn("Casts", ImGuiTableColumnFlags_WidthFixed, 70.0f);
            ImGui::TableHeadersRow();
            int n = 0;
            for (const auto& r : casterSpellRows) {
                ImGui::TableNextRow();
                ImGui::TableSetColumnIndex(0); ImGui::Text("%d", ++n);
                ImGui::TableSetColumnIndex(1); ImGui::TextColored(ImVec4(0.35f,0.82f,1.0f,1.0f), "%s", r.caster.c_str());
                ImGui::TableSetColumnIndex(2); ImGui::TextUnformatted(r.spell.c_str());
                ImGui::TableSetColumnIndex(3); ImGui::Text("%u", r.casts);
            }
            if (n == 0) {
                ImGui::TableNextRow();
                ImGui::TableSetColumnIndex(1);
                ImGui::TextDisabled("No spells detected for this fight.");
            }
            ImGui::EndTable();
        }
        if (ImGui::Button("Close", ImVec2(100, 28))) ImGui::CloseCurrentPopup();
        ImGui::EndPopup();
    }
    ImGui::EndChild();

    ImGui::Spacing();
    ImGui::BeginChild("##right_events_box", ImVec2(0, 0), true);
    ImGui::TextColored(ImVec4(1.0f, 0.55f, 0.18f, 1.0f), "TANK");
    ImGui::Separator();
    ImGui::TextColored(ImVec4(0.35f, 0.82f, 1.0f, 1.0f), "Tank Stats");

    struct HP_DpsTankRowForUi {
        std::string name;
        LiveTankRow stats;
    };

    std::vector<HP_DpsTankRowForUi> tankRowsForUi;
    int tankSelectedFightIndex = g_fullUiDpsSelectedFight.load();
    const bool tankCombiningSelectedFights = !g_dpsSelectedFights.empty();

    auto mergeTankRow = [&](LiveTankRow& dst, const LiveTankRow& src) {
        if (dst.firstMs == 0 || (src.firstMs > 0 && src.firstMs < dst.firstMs)) dst.firstMs = src.firstMs;
        if (src.lastMs > dst.lastMs) dst.lastMs = src.lastMs;
        dst.damage += src.damage;
        dst.hits += src.hits;
        dst.misses += src.misses;
        dst.dodges += src.dodges;
        dst.parries += src.parries;
        dst.ripostes += src.ripostes;
        dst.blocks += src.blocks;
        if (src.maxHit > dst.maxHit) dst.maxHit = src.maxHit;
        if (!tankCombiningSelectedFights || dst.hitEvents.size() < 600) {
            const size_t room = tankCombiningSelectedFights && dst.hitEvents.size() < 600 ? (600 - dst.hitEvents.size()) : src.hitEvents.size();
            if (src.hitEvents.size() <= room)
                dst.hitEvents.insert(dst.hitEvents.end(), src.hitEvents.begin(), src.hitEvents.end());
            else
                dst.hitEvents.insert(dst.hitEvents.end(), src.hitEvents.begin(), src.hitEvents.begin() + room);
        }
        if (!tankCombiningSelectedFights) {
            dst.lastHits.insert(dst.lastHits.end(), src.lastHits.begin(), src.lastHits.end());
            std::sort(dst.hitEvents.begin(), dst.hitEvents.end(), [](const LiveTankHitEvent& a, const LiveTankHitEvent& b){ return a.ms < b.ms; });
            std::sort(dst.lastHits.begin(), dst.lastHits.end(), [](const LiveTankHitEvent& a, const LiveTankHitEvent& b){ return a.ms < b.ms; });
            if (dst.lastHits.size() > 10)
                dst.lastHits.erase(dst.lastHits.begin(), dst.lastHits.begin() + (dst.lastHits.size() - 10));
        }
    };

    std::unordered_map<std::string, LiveTankRow> tankAcc;
    auto addTankRowsFromMap = [&](const std::unordered_map<std::string, LiveTankRow>& srcMap) {
        for (const auto& kv : srcMap) {
            if (kv.first.empty()) continue;
            if (kv.second.damage == 0 && HP_TankSwings(kv.second) == 0) continue;
            mergeTankRow(tankAcc[kv.first], kv.second);
        }
    };

    if (tankCombiningSelectedFights) {
        std::lock_guard<std::mutex> tk(g_completedTankMutex);
        for (int idx : g_dpsSelectedFights) {
            if (idx >= 0 && idx < (int)g_completedTankFights.size())
                addTankRowsFromMap(g_completedTankFights[(size_t)idx].tanks);
        }
    } else if (tankSelectedFightIndex >= 0) {
        std::lock_guard<std::mutex> tk(g_completedTankMutex);
        if (tankSelectedFightIndex < (int)g_completedTankFights.size())
            addTankRowsFromMap(g_completedTankFights[(size_t)tankSelectedFightIndex].tanks);
    } else {
        std::lock_guard<std::mutex> tk(g_liveTankMutex);
        addTankRowsFromMap(g_liveTank);
    }

    if (tankCombiningSelectedFights) {
        for (auto& kv : tankAcc) {
            std::sort(kv.second.hitEvents.begin(), kv.second.hitEvents.end(), [](const LiveTankHitEvent& a, const LiveTankHitEvent& b){ return a.ms < b.ms; });
            if (kv.second.hitEvents.size() > 600)
                kv.second.hitEvents.erase(kv.second.hitEvents.begin(), kv.second.hitEvents.end() - 600);
            kv.second.lastHits.clear();
            size_t start = kv.second.hitEvents.size() > 10 ? kv.second.hitEvents.size() - 10 : 0;
            kv.second.lastHits.insert(kv.second.lastHits.end(), kv.second.hitEvents.begin() + start, kv.second.hitEvents.end());
        }
    }

    auto flushTankAccumulatorToUi = [&]() {
        tankRowsForUi.clear();
        tankRowsForUi.reserve(tankAcc.size());
        for (auto& kv : tankAcc) {
            HP_DpsTankRowForUi row;
            row.name = kv.first;
            row.stats = std::move(kv.second);
            tankRowsForUi.push_back(std::move(row));
        }
    };
    flushTankAccumulatorToUi();

    // If tank rows are not present after a plugin reload, rebuild the basic
    // incoming-hit stats from the selected fight's saved log lines. This keeps
    // the Tank section tied to each saved fight instead of only live memory.
    if (tankRowsForUi.empty() && tankSelectedFightIndex >= 0) {
        CompletedDpsFight savedFight;
        bool haveSavedFight = false;
        {
            std::lock_guard<std::mutex> dk(g_completedDpsMutex);
            if (tankSelectedFightIndex < (int)g_completedDpsFights.size()) {
                savedFight = g_completedDpsFights[(size_t)tankSelectedFightIndex];
                haveSavedFight = true;
            }
        }
        if (haveSavedFight && !savedFight.logs.empty()) {
            std::unordered_set<std::string> pcNames;
            for (const auto& pkv : savedFight.players) {
                if (!pkv.first.empty() && !HP_ShouldHideDpsDisplayRow(pkv.first, savedFight.mob))
                    pcNames.insert(pkv.first);
            }
            {
                std::lock_guard<std::mutex> nk(g_statsMutex);
                for (const auto& nm : g_knownChars) if (!nm.empty()) pcNames.insert(nm);
            }

            auto isKnownPcForTank = [&](const std::string& nm) -> bool {
                if (nm.empty()) return false;
                if (pcNames.find(nm) != pcNames.end()) return true;
                for (const auto& pc : pcNames) if (HP_SameNameNoCase(pc, nm)) return true;
                return false;
            };
            auto stripLogPrefixForTank = [](const std::string& line) -> std::string {
                size_t rb = line.find(']');
                if (rb != std::string::npos && rb + 1 < line.size()) {
                    std::string out = line.substr(rb + 1);
                    Trim(out);
                    return out;
                }
                return line;
            };
            auto wallFromLogLineForTank = [&](const std::string& line) -> int64_t {
                size_t lb = line.find('[');
                size_t rb = line.find(']');
                if (lb == std::string::npos || rb == std::string::npos || rb <= lb + 1)
                    return savedFight.wallStarted;
                std::string ts = line.substr(lb + 1, rb - lb - 1);
                int hh = 0, mm = 0, ss = 0;
                char ap[3] = {0};
                if (std::sscanf(ts.c_str(), "%d:%d:%d %2s", &hh, &mm, &ss, ap) != 4)
                    return savedFight.wallStarted;
                std::time_t base = (std::time_t)(savedFight.wallStarted > 0 ? savedFight.wallStarted : HP_WallNow());
                std::tm tmv{};
#ifdef _WIN32
                localtime_s(&tmv, &base);
#else
                localtime_r(&base, &tmv);
#endif
                bool pm = (ap[0] == 'P' || ap[0] == 'p');
                bool am = (ap[0] == 'A' || ap[0] == 'a');
                if (pm && hh < 12) hh += 12;
                if (am && hh == 12) hh = 0;
                tmv.tm_hour = hh; tmv.tm_min = mm; tmv.tm_sec = ss;
                int64_t wall = (int64_t)std::mktime(&tmv);
                if (savedFight.wallStarted > 0 && wall < savedFight.wallStarted - 43200) wall += 86400;
                if (savedFight.wallStarted > 0 && wall > savedFight.wallStarted + 43200) wall -= 86400;
                return wall;
            };

            std::unordered_map<std::string, LiveTankRow> rebuiltTankRows;
            auto addSavedTankHit = [&](const std::string& target, uint64_t amount, const std::string& attacker, const std::string& type, int64_t wall) {
                if (target.empty() || amount == 0 || !isKnownPcForTank(target)) return;
                LiveTankRow& t = rebuiltTankRows[target];
                int64_t relMs = savedFight.startedMs;
                if (savedFight.wallStarted > 0 && wall > 0)
                    relMs = savedFight.startedMs + std::max<int64_t>(0, wall - savedFight.wallStarted) * 1000;
                if (t.firstMs == 0) t.firstMs = relMs;
                t.lastMs = relMs;
                t.damage += amount;
                t.hits += 1;
                if (amount > t.maxHit) t.maxHit = (uint32_t)std::min<uint64_t>(amount, UINT32_MAX);
                LiveTankHitEvent ev;
                ev.ms = relMs;
                ev.amount = (uint32_t)std::min<uint64_t>(amount, UINT32_MAX);
                ev.attacker = attacker.empty() ? savedFight.mob : attacker;
                ev.type = type.empty() ? std::string("Hit") : type;
                t.hitEvents.push_back(ev);
                t.lastHits.push_back(ev);
            };

            static const char* kTankMeleeVerbs[] = {
                " hits ", " slashes ", " crushes ", " pierces ", " bashes ", " kicks ",
                " claws ", " bites ", " gores ", " mauls ", " stings ", " punches ",
                " strikes ", " slices ", " smashes ", " rends ", " slams ", " backstabs ",
                " gnaws ", " slaps ", " pummels ", " mangles ", " chomps ", " sweeps ",
                " frenzies on ", " tail rakes "
            };

            for (const std::string& rawLine : savedFight.logs) {
                std::string msg = stripLogPrefixForTank(rawLine);
                if (msg.empty()) continue;
                int64_t wall = wallFromLogLineForTank(rawLine);

                size_t hitp = msg.find(" hit ");
                size_t forp = msg.find(" for ", hitp == std::string::npos ? 0 : hitp + 5);
                if (msg.find("non-melee damage") != std::string::npos && hitp != std::string::npos && forp != std::string::npos) {
                    std::string attacker = msg.substr(0, hitp); Trim(attacker);
                    std::string target = msg.substr(hitp + 5, forp - (hitp + 5)); Trim(target);
                    uint64_t amount = 0; const char* ep = nullptr;
                    if (ParseUintWithCommas(msg.c_str() + forp + 5, &amount, &ep))
                        addSavedTankHit(target, amount, attacker, "nonmelee", wall);
                    continue;
                }

                size_t taken = msg.find(" has taken ");
                if (taken != std::string::npos) {
                    std::string target = msg.substr(0, taken); Trim(target);
                    const char* pnum = msg.c_str() + taken + strlen(" has taken ");
                    uint64_t amount = 0; const char* after = nullptr;
                    if (ParseUintWithCommas(pnum, &amount, &after)) {
                        std::string attacker = savedFight.mob;
                        const char* byp = FindSubstr(after, " by ");
                        if (byp) { attacker.assign(byp + 4); Trim(attacker); }
                        addSavedTankHit(target, amount, attacker, "dot", wall);
                    }
                    continue;
                }

                size_t pdmg = msg.find("points of damage");
                if (pdmg == std::string::npos) pdmg = msg.find("point of damage");
                if (pdmg == std::string::npos || msg.find("non-melee damage") != std::string::npos) continue;
                forp = msg.rfind(" for ", pdmg);
                if (forp == std::string::npos) continue;
                uint64_t amount = 0; const char* ep = nullptr;
                if (!ParseUintWithCommas(msg.c_str() + forp + 5, &amount, &ep) || amount == 0) continue;
                std::string left = msg.substr(0, forp); Trim(left);
                size_t bestPos = std::string::npos, bestLen = 0;
                for (const char* v : kTankMeleeVerbs) {
                    size_t pos = left.rfind(v);
                    if (pos != std::string::npos && (bestPos == std::string::npos || pos > bestPos)) {
                        bestPos = pos; bestLen = strlen(v);
                    }
                }
                if (bestPos == std::string::npos) continue;
                std::string attacker = left.substr(0, bestPos); Trim(attacker);
                std::string target = left.substr(bestPos + bestLen); Trim(target);
                addSavedTankHit(target, amount, attacker, "melee", wall);
            }

            addTankRowsFromMap(rebuiltTankRows);
        }
    }


    // When multiple fights are selected, the completed tank archive may be empty
    // after a plugin reload. Rebuild combined Tank Stats / Spike DMG from each
    // selected fight's saved logs so combined DPS views do not show blanks.
    if (tankCombiningSelectedFights && tankRowsForUi.empty()) {
        static std::string s_cachedCombinedTankKey;
        static std::vector<HP_DpsTankRowForUi> s_cachedCombinedTankRows;
        std::string combinedTankKey = HP_BuildSelectedFightCacheKey() + "|tankLogs";
        if (combinedTankKey == s_cachedCombinedTankKey) {
            tankRowsForUi = s_cachedCombinedTankRows;
        } else {
        std::vector<CompletedDpsFight> selectedSavedFights;
        {
            std::lock_guard<std::mutex> dk(g_completedDpsMutex);
            for (int idx : g_dpsSelectedFights) {
                if (idx >= 0 && idx < (int)g_completedDpsFights.size())
                    selectedSavedFights.push_back(g_completedDpsFights[(size_t)idx]);
            }
        }
        for (const CompletedDpsFight& savedFight : selectedSavedFights) {
            if (savedFight.logs.empty()) continue;
            std::unordered_set<std::string> pcNames;
            for (const auto& pkv : savedFight.players) {
                if (!pkv.first.empty() && !HP_ShouldHideDpsDisplayRow(pkv.first, savedFight.mob))
                    pcNames.insert(pkv.first);
            }
            {
                std::lock_guard<std::mutex> nk(g_statsMutex);
                for (const auto& nm : g_knownChars) if (!nm.empty()) pcNames.insert(nm);
            }
            auto isKnownPcForTank = [&](const std::string& nm) -> bool {
                if (nm.empty()) return false;
                if (pcNames.find(nm) != pcNames.end()) return true;
                for (const auto& pc : pcNames) if (HP_SameNameNoCase(pc, nm)) return true;
                return false;
            };
            auto stripLogPrefixForTank = [](const std::string& line) -> std::string {
                size_t rb = line.find(']');
                if (rb != std::string::npos && rb + 1 < line.size()) { std::string out = line.substr(rb + 1); Trim(out); return out; }
                return line;
            };
            auto wallFromLogLineForTank = [&](const std::string& line) -> int64_t {
                size_t lb = line.find('['), rb = line.find(']');
                if (lb == std::string::npos || rb == std::string::npos || rb <= lb + 1) return savedFight.wallStarted;
                std::string ts = line.substr(lb + 1, rb - lb - 1);
                int hh = 0, mm = 0, ss = 0; char ap[3] = {0};
                if (std::sscanf(ts.c_str(), "%d:%d:%d %2s", &hh, &mm, &ss, ap) != 4) return savedFight.wallStarted;
                std::time_t base = (std::time_t)(savedFight.wallStarted > 0 ? savedFight.wallStarted : HP_WallNow());
                std::tm tmv{};
#ifdef _WIN32
                localtime_s(&tmv, &base);
#else
                localtime_r(&base, &tmv);
#endif
                bool pm = (ap[0] == 'P' || ap[0] == 'p'); bool am = (ap[0] == 'A' || ap[0] == 'a');
                if (pm && hh < 12) hh += 12; if (am && hh == 12) hh = 0;
                tmv.tm_hour = hh; tmv.tm_min = mm; tmv.tm_sec = ss;
                int64_t wall = (int64_t)std::mktime(&tmv);
                if (savedFight.wallStarted > 0 && wall < savedFight.wallStarted - 43200) wall += 86400;
                if (savedFight.wallStarted > 0 && wall > savedFight.wallStarted + 43200) wall -= 86400;
                return wall;
            };
            auto addSavedTankHit = [&](const std::string& target, uint64_t amount, const std::string& attacker, const std::string& type, int64_t wall) {
                if (target.empty() || amount == 0 || !isKnownPcForTank(target)) return;
                LiveTankRow temp;
                int64_t relMs = savedFight.startedMs;
                if (savedFight.wallStarted > 0 && wall > 0) relMs = savedFight.startedMs + std::max<int64_t>(0, wall - savedFight.wallStarted) * 1000;
                temp.firstMs = relMs; temp.lastMs = relMs; temp.damage = amount; temp.hits = 1; temp.maxHit = (uint32_t)std::min<uint64_t>(amount, UINT32_MAX);
                LiveTankHitEvent ev; ev.ms = relMs; ev.amount = (uint32_t)std::min<uint64_t>(amount, UINT32_MAX); ev.attacker = attacker.empty() ? savedFight.mob : attacker; ev.type = type.empty() ? std::string("Hit") : type;
                temp.hitEvents.push_back(ev); temp.lastHits.push_back(ev);
                mergeTankRow(tankAcc[target], temp);
            };
            static const char* kTankMeleeVerbsCombined[] = { " hits ", " slashes ", " crushes ", " pierces ", " bashes ", " kicks ", " claws ", " bites ", " gores ", " mauls ", " stings ", " punches ", " strikes ", " slices ", " smashes ", " rends ", " slams ", " backstabs ", " gnaws ", " slaps ", " pummels ", " mangles ", " chomps ", " sweeps ", " frenzies on ", " tail rakes " };
            for (const std::string& rawLine : savedFight.logs) {
                std::string msg = stripLogPrefixForTank(rawLine); if (msg.empty()) continue;
                int64_t wall = wallFromLogLineForTank(rawLine);
                size_t hitp = msg.find(" hit "); size_t forp = msg.find(" for ", hitp == std::string::npos ? 0 : hitp + 5);
                if (msg.find("non-melee damage") != std::string::npos && hitp != std::string::npos && forp != std::string::npos) {
                    std::string attacker = msg.substr(0, hitp); Trim(attacker); std::string target = msg.substr(hitp + 5, forp - (hitp + 5)); Trim(target);
                    uint64_t amount = 0; const char* ep = nullptr; if (ParseUintWithCommas(msg.c_str() + forp + 5, &amount, &ep)) addSavedTankHit(target, amount, attacker, "nonmelee", wall); continue;
                }
                size_t taken = msg.find(" has taken ");
                if (taken != std::string::npos) {
                    std::string target = msg.substr(0, taken); Trim(target); const char* pnum = msg.c_str() + taken + strlen(" has taken "); uint64_t amount = 0; const char* after = nullptr;
                    if (ParseUintWithCommas(pnum, &amount, &after)) { std::string attacker = savedFight.mob; const char* byp = FindSubstr(after, " by "); if (byp) { attacker.assign(byp + 4); Trim(attacker); } addSavedTankHit(target, amount, attacker, "dot", wall); } continue;
                }
                size_t pdmg = msg.find("points of damage"); if (pdmg == std::string::npos) pdmg = msg.find("point of damage");
                if (pdmg == std::string::npos || msg.find("non-melee damage") != std::string::npos) continue;
                forp = msg.rfind(" for ", pdmg); if (forp == std::string::npos) continue;
                uint64_t amount = 0; const char* ep = nullptr; if (!ParseUintWithCommas(msg.c_str() + forp + 5, &amount, &ep) || amount == 0) continue;
                std::string left = msg.substr(0, forp); Trim(left); size_t bestPos = std::string::npos, bestLen = 0;
                for (const char* v : kTankMeleeVerbsCombined) { size_t pos = left.rfind(v); if (pos != std::string::npos && (bestPos == std::string::npos || pos > bestPos)) { bestPos = pos; bestLen = strlen(v); } }
                if (bestPos == std::string::npos) continue;
                std::string attacker = left.substr(0, bestPos); Trim(attacker); std::string target = left.substr(bestPos + bestLen); Trim(target); addSavedTankHit(target, amount, attacker, "melee", wall);
            }
        }
        flushTankAccumulatorToUi();
        s_cachedCombinedTankKey = combinedTankKey;
        s_cachedCombinedTankRows = tankRowsForUi;
        }
    }

    std::sort(tankRowsForUi.begin(), tankRowsForUi.end(), [](const HP_DpsTankRowForUi& a, const HP_DpsTankRowForUi& b) {
        if (a.stats.damage != b.stats.damage) return a.stats.damage > b.stats.damage;
        return a.name < b.name;
    });

    static LiveTankRow s_dpsTankPopupStats;
    static std::string s_dpsTankPopupName;
    static int64_t s_dpsTankPopupWallBase = 0;
    static int64_t s_dpsTankPopupMsBase = 0;
    static bool s_dpsTankPopupValid = false;
    bool openDpsTankPopup = false;

    if (ImGui::BeginChild("##dps_tank_pc_list", ImVec2(0, 165.0f), true)) {
        // Keep this right-side list compact so long PC names fit. The full
        // riposte/parry/dodge/miss/hit breakdown is in the click popup.
        if (ImGui::BeginTable("##dps_tank_pc_table", 3, ImGuiTableFlags_RowBg | ImGuiTableFlags_BordersInnerH | ImGuiTableFlags_SizingStretchProp | ImGuiTableFlags_ScrollY)) {
            ImGui::TableSetupColumn("NAME", ImGuiTableColumnFlags_WidthStretch, 1.7f);
            ImGui::TableSetupColumn("Dmg", ImGuiTableColumnFlags_WidthFixed, 58.0f);
            ImGui::TableSetupColumn("Hits", ImGuiTableColumnFlags_WidthFixed, 50.0f);
            ImGui::TableHeadersRow();
            int tankRowId = 0;
            for (const auto& tr : tankRowsForUi) {
                ImGui::TableNextRow();
                ImGui::TableSetColumnIndex(0);
                std::string label = tr.name + "##dps_tank_pc_" + std::to_string(tankRowId++);
                ImGui::PushStyleColor(ImGuiCol_Text, ImVec4(0.25f, 0.85f, 1.0f, 1.0f));
                bool clicked = ImGui::Selectable(label.c_str(), false, ImGuiSelectableFlags_SpanAllColumns | ImGuiSelectableFlags_AllowItemOverlap);
                ImGui::PopStyleColor();
                if (ImGui::IsItemHovered()) {
                    ImGui::BeginTooltip();
                    ImGui::TextUnformatted("Click to view tanking stats for this PC.");
                    ImGui::EndTooltip();
                }
                if (clicked) {
                    s_dpsTankPopupName = tr.name;
                    s_dpsTankPopupStats = tr.stats;
                    s_dpsTankPopupValid = true;
                    if (tankSelectedFightIndex >= 0) {
                        std::lock_guard<std::mutex> dk(g_completedDpsMutex);
                        if (tankSelectedFightIndex < (int)g_completedDpsFights.size()) {
                            s_dpsTankPopupWallBase = g_completedDpsFights[(size_t)tankSelectedFightIndex].wallStarted;
                            s_dpsTankPopupMsBase = g_completedDpsFights[(size_t)tankSelectedFightIndex].startedMs;
                        }
                    } else {
                        std::lock_guard<std::mutex> dk(g_liveDpsMutex);
                        s_dpsTankPopupWallBase = g_liveDps.wallStarted;
                        s_dpsTankPopupMsBase = g_liveDps.startedMs;
                    }
                    openDpsTankPopup = true;
                }
                ImGui::TableSetColumnIndex(1); ImGui::Text("%s", HT_FormatShort(tr.stats.damage).c_str());
                ImGui::TableSetColumnIndex(2); ImGui::Text("%s", HT_FormatInteger(HP_TankSwings(tr.stats)).c_str());
            }
            if (tankRowsForUi.empty()) {
                ImGui::TableNextRow();
                ImGui::TableSetColumnIndex(0);
                ImGui::TextDisabled("No incoming tank damage recorded for this fight.");
            }
            ImGui::EndTable();
        }
    }
    ImGui::EndChild();

    struct HP_DpsTankSpikeUiRow {
        std::string name;
        LiveTankRow stats;
        uint64_t spike = 0;
        int64_t startMs = 0;
        int64_t endMs = 0;
    };
    auto calcTankSpike5s = [](const LiveTankRow& stats) -> std::pair<uint64_t, int64_t> {
        if (stats.hitEvents.empty()) return { 0, 0 };
        std::vector<LiveTankHitEvent> evs = stats.hitEvents;
        std::sort(evs.begin(), evs.end(), [](const LiveTankHitEvent& a, const LiveTankHitEvent& b) { return a.ms < b.ms; });
        uint64_t best = 0;
        int64_t bestStart = evs.front().ms;
        for (size_t i = 0; i < evs.size(); ++i) {
            uint64_t sum = 0;
            int64_t start = evs[i].ms;
            for (size_t j = i; j < evs.size(); ++j) {
                if (evs[j].ms - start > 5000) break;
                sum += evs[j].amount;
            }
            if (sum > best) { best = sum; bestStart = start; }
        }
        return { best, bestStart };
    };

    std::vector<HP_DpsTankSpikeUiRow> spikeRowsForUi;
    for (const auto& tr : tankRowsForUi) {
        auto spikeInfo = calcTankSpike5s(tr.stats);
        if (spikeInfo.first == 0) continue;
        // Only list meaningful spikes so the box stays useful and avoids spam.
        if (spikeInfo.first < 3000 && tr.stats.maxHit < 2500) continue;
        HP_DpsTankSpikeUiRow sr;
        sr.name = tr.name;
        sr.stats = tr.stats;
        sr.spike = spikeInfo.first;
        sr.startMs = spikeInfo.second;
        sr.endMs = spikeInfo.second + 5000;
        spikeRowsForUi.push_back(std::move(sr));
    }
    std::sort(spikeRowsForUi.begin(), spikeRowsForUi.end(), [](const HP_DpsTankSpikeUiRow& a, const HP_DpsTankSpikeUiRow& b) {
        if (a.spike != b.spike) return a.spike > b.spike;
        return a.name < b.name;
    });

    static LiveTankRow s_dpsTankSpikePopupStats;
    static std::string s_dpsTankSpikePopupName;
    static int64_t s_dpsTankSpikePopupStartMs = 0;
    static int64_t s_dpsTankSpikePopupEndMs = 0;
    static int64_t s_dpsTankSpikePopupWallBase = 0;
    static int64_t s_dpsTankSpikePopupMsBase = 0;
    static bool s_dpsTankSpikePopupValid = false;
    bool openDpsTankSpikePopup = false;

    ImGui::Spacing();
    ImGui::TextColored(ImVec4(1.0f, 0.55f, 0.18f, 1.0f), "Spike DMG");
    if (ImGui::BeginChild("##dps_tank_spike_list", ImVec2(0, 170.0f), true)) {
        if (ImGui::BeginTable("##dps_tank_spike_table", 3, ImGuiTableFlags_RowBg | ImGuiTableFlags_BordersInnerH | ImGuiTableFlags_SizingStretchProp | ImGuiTableFlags_ScrollY)) {
            ImGui::TableSetupColumn("NAME", ImGuiTableColumnFlags_WidthStretch, 1.7f);
            ImGui::TableSetupColumn("Spike", ImGuiTableColumnFlags_WidthFixed, 70.0f);
            ImGui::TableSetupColumn("Time", ImGuiTableColumnFlags_WidthFixed, 86.0f);
            ImGui::TableHeadersRow();
            int spikeRowId = 0;
            for (const auto& sr : spikeRowsForUi) {
                if (spikeRowId >= 12) break;
                int64_t wallStart = 0;
                if (tankSelectedFightIndex >= 0) {
                    std::lock_guard<std::mutex> dk(g_completedDpsMutex);
                    if (tankSelectedFightIndex < (int)g_completedDpsFights.size()) {
                        const auto& f = g_completedDpsFights[(size_t)tankSelectedFightIndex];
                        if (f.wallStarted > 0 && f.startedMs > 0 && sr.startMs >= f.startedMs)
                            wallStart = f.wallStarted + std::max<int64_t>(0, (sr.startMs - f.startedMs) / 1000);
                    }
                } else {
                    std::lock_guard<std::mutex> dk(g_liveDpsMutex);
                    if (g_liveDps.wallStarted > 0 && g_liveDps.startedMs > 0 && sr.startMs >= g_liveDps.startedMs)
                        wallStart = g_liveDps.wallStarted + std::max<int64_t>(0, (sr.startMs - g_liveDps.startedMs) / 1000);
                }
                ImGui::TableNextRow();
                ImGui::TableSetColumnIndex(0);
                std::string label = sr.name + "##dps_tank_spike_" + std::to_string(spikeRowId++);
                ImGui::PushStyleColor(ImGuiCol_Text, ImVec4(0.25f, 0.85f, 1.0f, 1.0f));
                bool clicked = ImGui::Selectable(label.c_str(), false, ImGuiSelectableFlags_SpanAllColumns | ImGuiSelectableFlags_AllowItemOverlap);
                ImGui::PopStyleColor();
                if (ImGui::IsItemHovered()) ImGui::SetTooltip("Click to view the 5 second damage spike and heals.");
                if (clicked) {
                    s_dpsTankSpikePopupName = sr.name;
                    s_dpsTankSpikePopupStats = sr.stats;
                    s_dpsTankSpikePopupStartMs = sr.startMs;
                    s_dpsTankSpikePopupEndMs = sr.endMs;
                    s_dpsTankSpikePopupValid = true;
                    if (tankSelectedFightIndex >= 0) {
                        std::lock_guard<std::mutex> dk(g_completedDpsMutex);
                        if (tankSelectedFightIndex < (int)g_completedDpsFights.size()) {
                            s_dpsTankSpikePopupWallBase = g_completedDpsFights[(size_t)tankSelectedFightIndex].wallStarted;
                            s_dpsTankSpikePopupMsBase = g_completedDpsFights[(size_t)tankSelectedFightIndex].startedMs;
                        }
                    } else {
                        std::lock_guard<std::mutex> dk(g_liveDpsMutex);
                        s_dpsTankSpikePopupWallBase = g_liveDps.wallStarted;
                        s_dpsTankSpikePopupMsBase = g_liveDps.startedMs;
                    }
                    openDpsTankSpikePopup = true;
                }
                ImGui::TableSetColumnIndex(1); ImGui::Text("%s", HT_FormatShort(sr.spike).c_str());
                ImGui::TableSetColumnIndex(2); ImGui::TextDisabled("%s", wallStart > 0 ? HP_FormatTimeWithSeconds(wallStart).c_str() : "--:--:--");
            }
            if (spikeRowsForUi.empty()) {
                ImGui::TableNextRow();
                ImGui::TableSetColumnIndex(0); ImGui::TextDisabled("No spike damage recorded.");
            }
            ImGui::EndTable();
        }
    }
    ImGui::EndChild();

    // ---------------------------------------------------------------------
    // Compare DPS panel (right side, under Spike DMG)
    // Opens as a real popup/modal, but uses a copied snapshot of the current
    // player rows.  The earlier versions crashed because the compare window
    // was drawing from the parent DPS row data while Select All was active and
    // the right-side child/table stack was still being built.  Other popups work
    // because they copy the needed data first; this now does the same.
    // ---------------------------------------------------------------------
    ImGui::Spacing();
    static bool s_requestDpsComparePopup = false;
    static bool s_dpsComparePopupOpen = false;
    static std::string s_compareA;
    static std::string s_compareB;
    static bool s_compareReady = false;
    static int s_compareDur = 0;
    struct HP_DpsCompareSnapshotRow {
        std::string name;
        uint64_t dmg = 0;
        uint64_t melee = 0;
        uint64_t spell = 0;
        uint64_t dot = 0;
        uint64_t proc = 0;
        uint64_t pet = 0;
        uint64_t swarm = 0;
        uint32_t hits = 0;
        uint32_t maxHit = 0;
    };
    static std::vector<HP_DpsCompareSnapshotRow> s_compareRows;
    static std::unordered_map<std::string, std::unordered_map<std::string, uint32_t>> s_cachedCompareCasts;
    static std::vector<std::string> s_cachedCompareFightLogs;
    static std::unordered_map<std::string, std::unordered_map<std::string, uint64_t>> s_cachedCompareMeleeDmg;
    static std::unordered_map<std::string, std::unordered_map<std::string, uint32_t>> s_cachedCompareMeleeHits;
    struct HP_DpsCompareMeleeDetailRow {
        std::string timeText;
        std::string sinceText;
        std::string action;
        uint64_t damage = 0;
        int secondsOfDay = -1;
    };
    static std::unordered_map<std::string, std::vector<HP_DpsCompareMeleeDetailRow>> s_cachedCompareMeleeDetails;
    static bool s_requestMeleeDetailPopup = false;
    static bool s_meleeDetailPopupOpen = false;
    static std::string s_meleeDetailPlayer;

    auto refreshDpsCompareFightLogs = [&]() {
        s_cachedCompareFightLogs.clear();

        auto formatEqLogTimestampFromWall = [](int64_t wall) -> std::string {
            if (wall <= 0) return std::string();
            std::time_t t = static_cast<std::time_t>(wall);
            std::tm tmv{};
#ifdef _WIN32
            localtime_s(&tmv, &t);
#else
            localtime_r(&t, &tmv);
#endif
            char buf[64] = { 0 };
            std::strftime(buf, sizeof(buf), "[%a %b %d %H:%M:%S %Y] ", &tmv);
            return std::string(buf);
        };

        auto pushFightLogWithFallbackTime = [&](const CompletedDpsFight& f, const std::string& line) {
            // Older saved fights and some combined-fight paths can contain raw
            // combat text without the EQ [date time] prefix.  The melee hit-log
            // popup reads that prefix for the Time column, so synthesize one
            // from the saved fight wall clock instead of showing blanks.
            if (!line.empty() && line[0] == '[') {
                s_cachedCompareFightLogs.push_back(line);
                return;
            }
            int64_t wall = f.wallStarted > 0 ? f.wallStarted : f.wallEnded;
            std::string prefix = formatEqLogTimestampFromWall(wall);
            s_cachedCompareFightLogs.push_back(prefix.empty() ? line : (prefix + line));
        };

        if (!g_dpsSelectedFights.empty()) {
            std::lock_guard<std::mutex> lk(g_completedDpsMutex);
            for (int idx : g_dpsSelectedFights) {
                if (idx < 0 || idx >= (int)g_completedDpsFights.size()) continue;
                const auto& f = g_completedDpsFights[(size_t)idx];
                for (const auto& line : f.logs)
                    pushFightLogWithFallbackTime(f, line);
            }
            return;
        }

        const int selectedFight = g_fullUiDpsSelectedFight.load();
        if (selectedFight >= 0) {
            std::lock_guard<std::mutex> lk(g_completedDpsMutex);
            if (selectedFight < (int)g_completedDpsFights.size()) {
                const auto& f = g_completedDpsFights[(size_t)selectedFight];
                for (const auto& line : f.logs)
                    pushFightLogWithFallbackTime(f, line);
            }
            return;
        }

        {
            std::lock_guard<std::mutex> lk(g_liveDpsMutex);
            for (const auto& line : g_liveDps.logs)
                s_cachedCompareFightLogs.push_back(line);
        }
    };

    auto buildDpsCompareMeleeBreakdown = [&]() {
        s_cachedCompareMeleeDmg.clear();
        s_cachedCompareMeleeHits.clear();
        s_cachedCompareMeleeDetails.clear();

        auto extractLogTimeText = [](const std::string& rawLine) -> std::string {
            if (rawLine.empty() || rawLine[0] != '[') return std::string("--");
            size_t rb = rawLine.find(']');
            if (rb == std::string::npos || rb <= 1) return std::string("--");
            std::string inside = rawLine.substr(1, rb - 1);
            std::istringstream iss(inside);
            std::string dow, mon, day, clock, year;
            if (iss >> dow >> mon >> day >> clock) {
                if (!mon.empty() && !day.empty() && !clock.empty())
                    return mon + " " + day + " " + clock;
            }
            return inside;
        };

        auto extractSecondsOfDay = [](const std::string& timeText) -> int {
            size_t p = timeText.rfind(' ');
            std::string clock = (p == std::string::npos) ? timeText : timeText.substr(p + 1);
            if (clock.size() < 8) return -1;
            if (!std::isdigit((unsigned char)clock[0]) || !std::isdigit((unsigned char)clock[1]) ||
                clock[2] != ':' || !std::isdigit((unsigned char)clock[3]) || !std::isdigit((unsigned char)clock[4]) ||
                clock[5] != ':' || !std::isdigit((unsigned char)clock[6]) || !std::isdigit((unsigned char)clock[7])) return -1;
            int h = (clock[0] - '0') * 10 + (clock[1] - '0');
            int m = (clock[3] - '0') * 10 + (clock[4] - '0');
            int sec = (clock[6] - '0') * 10 + (clock[7] - '0');
            return h * 3600 + m * 60 + sec;
        };

        auto formatSinceSeconds = [](int delta) -> std::string {
            if (delta <= 0) return std::string("-");
            char buf[32];
            int mm = delta / 60;
            int ss = delta % 60;
#ifdef _WIN32
            sprintf_s(buf, "%02d:%02d", mm, ss);
#else
            std::snprintf(buf, sizeof(buf), "%02d:%02d", mm, ss);
#endif
            return std::string(buf);
        };

        auto titleVerbForDetail = [](std::string v) -> std::string {
            Trim(v);
            if (v.empty()) return std::string("Melee");
            v[0] = (char)std::toupper((unsigned char)v[0]);
            return v;
        };

        static const char* kCompareMeleeVerbs[] = {
            " hits ", " slashes ", " crushes ", " pierces ", " bashes ", " kicks ",
            " claws ", " bites ", " gores ", " mauls ", " stings ", " punches ",
            " strikes ", " slices ", " smashes ", " rends ", " slams ", " backstabs ",
            " gnaws ", " slaps ", " pummels ", " mangles ", " chomps ", " sweeps ",
            " frenzies on ", " tail rakes ", " burns ", " freezes ", " shoots ",
        };

        auto normalizeMeleeVerb = [](std::string v) -> std::string {
            Trim(v);
            std::string l = LowerCopy(v);
            if (l == "hits") return "Hit";
            if (l == "slashes") return "Slash";
            if (l == "crushes") return "Blunt / Crush";
            if (l == "pierces") return "Pierce";
            if (l == "bashes") return "Bash";
            if (l == "kicks") return "Kick";
            if (l == "backstabs") return "Backstab";
            if (l == "punches") return "Punch";
            if (l == "claws") return "Claw";
            if (l == "bites") return "Bite";
            if (l == "gores") return "Gore";
            if (l == "mauls") return "Maul";
            if (l == "stings") return "Sting";
            if (l == "strikes") return "Strike";
            if (l == "slices") return "Slice";
            if (l == "smashes") return "Smash";
            if (l == "rends") return "Rend";
            if (l == "slams") return "Slam";
            if (l == "gnaws") return "Gnaw";
            if (l == "slaps") return "Slap";
            if (l == "pummels") return "Pummel";
            if (l == "mangles") return "Mangle";
            if (l == "chomps") return "Chomp";
            if (l == "sweeps") return "Sweep";
            if (l == "frenzies on") return "Frenzy";
            if (l == "tail rakes") return "Tail Rake";
            if (l == "burns") return "Burn";
            if (l == "freezes") return "Freeze";
            if (l == "shoots") return "Shoot";
            if (v.empty()) return "Melee";
            v[0] = (char)std::toupper((unsigned char)v[0]);
            return v;
        };

        for (const std::string& rawLine : s_cachedCompareFightLogs) {
            std::string msg = rawLine;
            const char* stripped = StripLogTimestamp(msg.c_str());
            if (stripped && stripped != msg.c_str()) msg = stripped;

            size_t pdmg = msg.find("points of damage");
            if (pdmg == std::string::npos) pdmg = msg.find("point of damage");
            if (pdmg == std::string::npos || msg.find("non-melee damage") != std::string::npos) continue;

            size_t forp = msg.rfind(" for ", pdmg);
            if (forp == std::string::npos) continue;

            uint64_t amount = 0;
            const char* endp = nullptr;
            if (!ParseUintWithCommas(msg.c_str() + forp + 5, &amount, &endp) || amount == 0) continue;

            std::string left = msg.substr(0, forp);
            Trim(left);
            if (left.empty()) continue;

            size_t bestPos = std::string::npos;
            size_t bestLen = 0;
            std::string bestVerb;
            for (const char* v : kCompareMeleeVerbs) {
                size_t pos = left.rfind(v);
                if (pos != std::string::npos && (bestPos == std::string::npos || pos > bestPos)) {
                    bestPos = pos;
                    bestLen = std::strlen(v);
                    bestVerb = v;
                }
            }
            if (bestPos == std::string::npos) continue;

            std::string attacker = left.substr(0, bestPos);
            Trim(attacker);
            if (attacker.empty()) continue;
            if (attacker == "You" || attacker == "YOU" || attacker == "you") continue;

            std::string displayName = HP_GetPetCombinedDisplayName(attacker);
            if (displayName.empty()) displayName = attacker;
            std::string verbLabel = normalizeMeleeVerb(bestVerb);

            s_cachedCompareMeleeDmg[displayName][verbLabel] += amount;
            s_cachedCompareMeleeHits[displayName][verbLabel] += 1;

            HP_DpsCompareMeleeDetailRow detail;
            detail.timeText = extractLogTimeText(rawLine);
            detail.secondsOfDay = extractSecondsOfDay(detail.timeText);
            detail.action = titleVerbForDetail(bestVerb);
            detail.damage = amount;
            s_cachedCompareMeleeDetails[displayName].push_back(std::move(detail));
        }

        for (auto& kv : s_cachedCompareMeleeDetails) {
            int prevSec = -1;
            for (auto& row : kv.second) {
                row.sinceText = (prevSec >= 0 && row.secondsOfDay >= 0) ? formatSinceSeconds(row.secondsOfDay - prevSec) : std::string("-");
                if (row.secondsOfDay >= 0) prevSec = row.secondsOfDay;
            }
        }
    };

    ImGui::PushStyleColor(ImGuiCol_ChildBg, IM_COL32(7, 10, 24, 235));
    ImGui::PushStyleColor(ImGuiCol_Border, IM_COL32(120, 70, 220, 185));
    ImGui::BeginChild("##dps_compare_box", ImVec2(0, 118.0f), true);
    ImGui::TextColored(ImVec4(0.78f, 0.42f, 1.0f, 1.0f), "COMPARE DPS");
    ImGui::Separator();
    ImGui::TextDisabled("Compare players, spells/discs, and damage.");
    ImGui::Spacing();
    ImGui::PushStyleColor(ImGuiCol_Text, ImVec4(0.20f, 1.00f, 0.20f, 1.0f));
    if (ImGui::Selectable("OPEN DPS COMPARE >>", false, ImGuiSelectableFlags_SpanAllColumns)) {
        s_compareRows.clear();
        s_compareRows.reserve(rows.size());
        for (const auto& r : rows) {
            if (r.name.empty()) continue;
            HP_DpsCompareSnapshotRow cr;
            cr.name = r.name;
            cr.dmg = r.dmg;
            cr.melee = r.melee;
            cr.spell = r.spell;
            cr.dot = r.dot;
            cr.proc = r.proc;
            cr.pet = r.pet;
            cr.swarm = r.swarm;
            cr.hits = r.hits;
            cr.maxHit = r.maxHit;
            s_compareRows.push_back(std::move(cr));
        }
        s_compareDur = std::max(1, dur);
        s_compareReady = false;
        s_cachedCompareCasts.clear();
        s_cachedCompareMeleeDmg.clear();
        s_cachedCompareMeleeHits.clear();
        s_cachedCompareMeleeDetails.clear();
        refreshDpsCompareFightLogs();
        if (s_compareRows.empty()) {
            s_compareA.clear();
            s_compareB.clear();
        } else {
            bool haveA = false, haveB = false;
            for (const auto& r : s_compareRows) {
                if (r.name == s_compareA) haveA = true;
                if (r.name == s_compareB) haveB = true;
            }
            if (!haveA) s_compareA = s_compareRows[0].name;
            if (!haveB || s_compareB == s_compareA) {
                s_compareB.clear();
                for (const auto& r : s_compareRows) {
                    if (r.name != s_compareA) { s_compareB = r.name; break; }
                }
            }
        }
        s_requestDpsComparePopup = true;
        s_dpsComparePopupOpen = true;
    }
    ImGui::PopStyleColor();
    ImGui::EndChild();
    ImGui::PopStyleColor(2);

    // ---------------------------------------------------------------------
    // Compare Mob Fights panel (right side, under Compare DPS)
    // Opens a separate popup the same size as DPS Compare.  Each fight choice
    // includes mob name + date/time + duration + total damage so same-name
    // bosses can be distinguished.
    // ---------------------------------------------------------------------
    ImGui::Spacing();
    static bool s_requestMobComparePopup = false;
    static bool s_mobComparePopupOpen = false;
    static int s_mobCompareA = -1;
    static int s_mobCompareB = -1;
    static char s_mobCompareSearchA[128] = "";
    static char s_mobCompareSearchB[128] = "";

    struct HP_MobCompareFightSnapshot {
        int index = -1;
        std::string mob;
        std::string label;
        int64_t wall = 0;
        int duration = 1;
        uint64_t total = 0;
        std::unordered_map<std::string, LiveDpsRow> players;
        std::unordered_map<std::string, uint32_t> spellCasts;
    };
    static std::vector<HP_MobCompareFightSnapshot> s_mobCompareFights;

    auto rebuildMobCompareSnapshot = [&]() {
        s_mobCompareFights.clear();
        std::vector<CompletedDpsFight> allFights;
        { std::lock_guard<std::mutex> lk(g_completedDpsMutex); allFights = g_completedDpsFights; }

        for (int i = 0; i < (int)allFights.size(); ++i) {
            const auto& f = allFights[(size_t)i];
            if (!HP_FightPassesDpsFilters(f)) continue;

            HP_MobCompareFightSnapshot fs;
            fs.index = i;
            fs.mob = f.mob;
            fs.wall = f.wallEnded > 0 ? f.wallEnded : f.wallStarted;
            fs.duration = (int)std::max<int64_t>(1, (f.endedMs - f.startedMs) / 1000);
            fs.total = f.total;
            fs.players = f.players;
            fs.spellCasts = f.spellCasts;

            std::ostringstream label;
            label << fs.mob
                  << "  |  " << HP_FormatDateTimeLong(fs.wall)
                  << "  |  " << (fs.duration / 60) << ":" << (fs.duration % 60 < 10 ? "0" : "") << (fs.duration % 60)
                  << "  |  " << HT_FormatShort(fs.total);
            fs.label = label.str();
            s_mobCompareFights.push_back(std::move(fs));
        }

        if (s_mobCompareA < 0 || s_mobCompareA >= (int)s_mobCompareFights.size()) s_mobCompareA = s_mobCompareFights.empty() ? -1 : 0;
        if (s_mobCompareB < 0 || s_mobCompareB >= (int)s_mobCompareFights.size() || s_mobCompareB == s_mobCompareA) {
            s_mobCompareB = -1;
            for (int i = 0; i < (int)s_mobCompareFights.size(); ++i) {
                if (i != s_mobCompareA) { s_mobCompareB = i; break; }
            }
        }
    };

    ImGui::PushStyleColor(ImGuiCol_ChildBg, IM_COL32(7, 10, 24, 235));
    ImGui::PushStyleColor(ImGuiCol_Border, IM_COL32(120, 70, 220, 185));
    ImGui::BeginChild("##dps_mob_compare_box", ImVec2(0, 126.0f), true);
    ImGui::TextColored(ImVec4(0.78f, 0.42f, 1.0f, 1.0f), "COMPARE MOB FIGHTS");
    ImGui::Separator();
    ImGui::TextDisabled("Compare two separate mob fights side by side.");
    ImGui::TextDisabled("Fight choices include date/time to separate same-name bosses.");
    ImGui::Spacing();
    ImGui::PushStyleColor(ImGuiCol_Text, ImVec4(0.20f, 1.00f, 0.20f, 1.0f));
    if (ImGui::Selectable("OPEN MOB FIGHT COMPARE >>", false, ImGuiSelectableFlags_SpanAllColumns)) {
        rebuildMobCompareSnapshot();
        s_requestMobComparePopup = true;
        s_mobComparePopupOpen = true;
    }
    ImGui::PopStyleColor();
    ImGui::EndChild();
    ImGui::PopStyleColor(2);

    if (s_requestMobComparePopup) {
        ImGui::OpenPopup("Mob Fight Compare##dps_mob_compare_modal");
        s_requestMobComparePopup = false;
    }

    ImGui::SetNextWindowSize(ImVec2(1400.0f, 900.0f), ImGuiCond_Appearing);
    ImGui::SetNextWindowSizeConstraints(ImVec2(1200.0f, 800.0f), ImVec2(FLT_MAX, FLT_MAX));
    ImGui::SetNextWindowPos(ImGui::GetMainViewport()->GetCenter(), ImGuiCond_Appearing, ImVec2(0.5f, 0.5f));
    if (ImGui::BeginPopupModal("Mob Fight Compare##dps_mob_compare_modal", &s_mobComparePopupOpen, ImGuiWindowFlags_NoCollapse)) {
        ImGui::TextColored(ImVec4(0.78f, 0.42f, 1.0f, 1.0f), "Compare Mob Fights");
        ImGui::TextDisabled("Search and pick two fights. Same-name bosses are listed with date/time, duration, and damage.");
        ImGui::Separator();

        if (s_mobCompareFights.empty()) {
            ImGui::TextDisabled("No completed fights match the current DPS filters/search.");
        } else {
            auto drawFightPicker = [&](const char* title, int& selected, char* searchBuf, const char* childId) {
                ImGui::TextColored(ImVec4(0.32f, 0.72f, 1.0f, 1.0f), "%s", title);
                ImGui::SetNextItemWidth(-FLT_MIN);
                ImGui::InputTextWithHint((std::string("##search_") + childId).c_str(), "Search mob name or date/time...", searchBuf, 128);

                std::string selectedText = (selected >= 0 && selected < (int)s_mobCompareFights.size()) ? s_mobCompareFights[(size_t)selected].label : std::string("--");
                ImGui::TextDisabled("Selected: %s", selectedText.c_str());

                if (ImGui::BeginChild(childId, ImVec2(0, 235.0f), true, ImGuiWindowFlags_AlwaysVerticalScrollbar)) {
                    int shownChoices = 0;
                    for (int i = 0; i < (int)s_mobCompareFights.size(); ++i) {
                        const auto& f = s_mobCompareFights[(size_t)i];
                        if (searchBuf && searchBuf[0] && !HP_ContainsNoCase(f.label, searchBuf)) continue;

                        ImGui::PushID((std::string(childId) + "_" + std::to_string(i)).c_str());
                        bool isSelected = (selected == i);
                        if (ImGui::Selectable(f.label.c_str(), isSelected)) selected = i;
                        ImGui::PopID();

                        if (++shownChoices >= 250) {
                            ImGui::TextDisabled("Showing first 250 matches. Narrow the search for older fights.");
                            break;
                        }
                    }
                    if (shownChoices == 0) ImGui::TextDisabled("No matching fights.");
                }
                ImGui::EndChild();
            };

            if (ImGui::BeginTable("##mob_compare_picker_table", 2, ImGuiTableFlags_SizingStretchSame | ImGuiTableFlags_BordersInnerV)) {
                ImGui::TableNextRow();
                ImGui::TableSetColumnIndex(0);
                drawFightPicker("Fight A", s_mobCompareA, s_mobCompareSearchA, "mob_compare_a_list");
                ImGui::TableSetColumnIndex(1);
                drawFightPicker("Fight B", s_mobCompareB, s_mobCompareSearchB, "mob_compare_b_list");
                ImGui::EndTable();
            }

            ImGui::Spacing();
            if (ImGui::Button("REFRESH FROM CURRENT FILTERS", ImVec2(230.0f, 28.0f))) {
                rebuildMobCompareSnapshot();
            }
            ImGui::SameLine();
            if (ImGui::Button("Close", ImVec2(100.0f, 28.0f))) {
                s_mobComparePopupOpen = false;
                ImGui::CloseCurrentPopup();
            }

            bool haveFightA = (s_mobCompareA >= 0 && s_mobCompareA < (int)s_mobCompareFights.size());
            bool haveFightB = (s_mobCompareB >= 0 && s_mobCompareB < (int)s_mobCompareFights.size());
            if (haveFightA && haveFightB && s_mobCompareA != s_mobCompareB) {
                const auto& fa = s_mobCompareFights[(size_t)s_mobCompareA];
                const auto& fb = s_mobCompareFights[(size_t)s_mobCompareB];

                auto fightRaidDps = [](const HP_MobCompareFightSnapshot& f) -> uint64_t {
                    return f.duration > 0 ? f.total / (uint64_t)f.duration : 0;
                };
                auto maxHitForFight = [](const HP_MobCompareFightSnapshot& f) -> uint32_t {
                    uint32_t m = 0;
                    for (const auto& kv : f.players) m = std::max(m, kv.second.maxHit);
                    return m;
                };

                ImGui::Spacing();
                if (ImGui::BeginTable("##mob_compare_summary_table", 3, ImGuiTableFlags_RowBg | ImGuiTableFlags_BordersInnerH | ImGuiTableFlags_SizingStretchProp)) {
                    ImGui::TableSetupColumn("Fight Summary", ImGuiTableColumnFlags_WidthStretch, 0.85f);
                    ImGui::TableSetupColumn("Fight A", ImGuiTableColumnFlags_WidthStretch, 1.25f);
                    ImGui::TableSetupColumn("Fight B", ImGuiTableColumnFlags_WidthStretch, 1.25f);
                    ImGui::TableHeadersRow();
#define HP_MOB_CMP_SUM_ROW(label, aval, bval) \
                    ImGui::TableNextRow(); \
                    ImGui::TableSetColumnIndex(0); ImGui::TextDisabled("%s", label); \
                    ImGui::TableSetColumnIndex(1); ImGui::TextUnformatted((aval).c_str()); \
                    ImGui::TableSetColumnIndex(2); ImGui::TextUnformatted((bval).c_str())
                    HP_MOB_CMP_SUM_ROW("Mob", fa.mob, fb.mob);
                    HP_MOB_CMP_SUM_ROW("Date / Time", HP_FormatDateTimeLong(fa.wall), HP_FormatDateTimeLong(fb.wall));
                    HP_MOB_CMP_SUM_ROW("Duration", std::to_string(fa.duration) + "s", std::to_string(fb.duration) + "s");
                    HP_MOB_CMP_SUM_ROW("Total Damage", HT_FormatShort(fa.total), HT_FormatShort(fb.total));
                    HP_MOB_CMP_SUM_ROW("Raid DPS", HT_FormatInteger(fightRaidDps(fa)), HT_FormatInteger(fightRaidDps(fb)));
                    HP_MOB_CMP_SUM_ROW("Players", HT_FormatInteger((uint64_t)fa.players.size()), HT_FormatInteger((uint64_t)fb.players.size()));
                    HP_MOB_CMP_SUM_ROW("Max Hit", HT_FormatInteger(maxHitForFight(fa)), HT_FormatInteger(maxHitForFight(fb)));
#undef HP_MOB_CMP_SUM_ROW
                    ImGui::EndTable();
                }

                std::vector<std::pair<std::string, LiveDpsRow>> playersA;
                std::vector<std::pair<std::string, LiveDpsRow>> playersB;
                playersA.reserve(fa.players.size());
                playersB.reserve(fb.players.size());

                for (const auto& kv : fa.players) {
                    if (!kv.first.empty() && kv.second.total > 0)
                        playersA.push_back(kv);
                }
                for (const auto& kv : fb.players) {
                    if (!kv.first.empty() && kv.second.total > 0)
                        playersB.push_back(kv);
                }

                auto playerDamageSort = [](const auto& a, const auto& b) {
                    if (a.second.total != b.second.total) return a.second.total > b.second.total;
                    return a.first < b.first;
                };
                std::sort(playersA.begin(), playersA.end(), playerDamageSort);
                std::sort(playersB.begin(), playersB.end(), playerDamageSort);

                size_t maxPlayerRows = std::max(playersA.size(), playersB.size());

                ImGui::Spacing();
                ImGui::TextColored(ImVec4(0.32f, 0.72f, 1.0f, 1.0f), "Player DPS Side by Side");
                ImGui::TextDisabled("Each side only lists players who were present on that specific fight.");
                if (ImGui::BeginTable("##mob_compare_player_table", 6, ImGuiTableFlags_RowBg | ImGuiTableFlags_BordersInnerH | ImGuiTableFlags_SizingStretchProp | ImGuiTableFlags_ScrollY, ImVec2(-FLT_MIN, 235.0f))) {
                    std::string fightAHeader = std::string("Fight A Player (") + std::to_string(playersA.size()) + ")";
                    std::string fightBHeader = std::string("Fight B Player (") + std::to_string(playersB.size()) + ")";
                    ImGui::TableSetupColumn(fightAHeader.c_str(), ImGuiTableColumnFlags_WidthStretch, 1.1f);
                    ImGui::TableSetupColumn("Fight A Dmg", ImGuiTableColumnFlags_WidthStretch, 0.75f);
                    ImGui::TableSetupColumn("Fight A DPS", ImGuiTableColumnFlags_WidthStretch, 0.70f);
                    ImGui::TableSetupColumn(fightBHeader.c_str(), ImGuiTableColumnFlags_WidthStretch, 1.1f);
                    ImGui::TableSetupColumn("Fight B Dmg", ImGuiTableColumnFlags_WidthStretch, 0.75f);
                    ImGui::TableSetupColumn("Fight B DPS", ImGuiTableColumnFlags_WidthStretch, 0.70f);
                    ImGui::TableSetupScrollFreeze(0, 1);
                    ImGui::TableHeadersRow();

                    for (size_t row = 0; row < maxPlayerRows; ++row) {
                        ImGui::TableNextRow();

                        ImGui::TableSetColumnIndex(0);
                        if (row < playersA.size()) ImGui::TextUnformatted(playersA[row].first.c_str());
                        else ImGui::TextDisabled("--");

                        ImGui::TableSetColumnIndex(1);
                        if (row < playersA.size()) ImGui::Text("%s", HT_FormatShort(playersA[row].second.total).c_str());
                        else ImGui::TextDisabled("--");

                        ImGui::TableSetColumnIndex(2);
                        if (row < playersA.size()) {
                            uint64_t adps = playersA[row].second.total / (uint64_t)std::max(1, fa.duration);
                            ImGui::Text("%s", HT_FormatInteger(adps).c_str());
                        } else ImGui::TextDisabled("--");

                        ImGui::TableSetColumnIndex(3);
                        if (row < playersB.size()) ImGui::TextUnformatted(playersB[row].first.c_str());
                        else ImGui::TextDisabled("--");

                        ImGui::TableSetColumnIndex(4);
                        if (row < playersB.size()) ImGui::Text("%s", HT_FormatShort(playersB[row].second.total).c_str());
                        else ImGui::TextDisabled("--");

                        ImGui::TableSetColumnIndex(5);
                        if (row < playersB.size()) {
                            uint64_t bdps = playersB[row].second.total / (uint64_t)std::max(1, fb.duration);
                            ImGui::Text("%s", HT_FormatInteger(bdps).c_str());
                        } else ImGui::TextDisabled("--");
                    }

                    if (maxPlayerRows == 0) {
                        ImGui::TableNextRow();
                        ImGui::TableSetColumnIndex(0);
                        ImGui::TextDisabled("No player DPS saved for these fights.");
                    }
                    ImGui::EndTable();
                }

                std::unordered_set<std::string> spellUnion;
                for (const auto& kv : fa.spellCasts) if (!kv.first.empty()) spellUnion.insert(kv.first);
                for (const auto& kv : fb.spellCasts) if (!kv.first.empty()) spellUnion.insert(kv.first);
                std::vector<std::string> spellList(spellUnion.begin(), spellUnion.end());
                std::sort(spellList.begin(), spellList.end(), [&](const std::string& x, const std::string& y) {
                    uint32_t ax = fa.spellCasts.count(x) ? fa.spellCasts.at(x) : 0;
                    uint32_t bx = fb.spellCasts.count(x) ? fb.spellCasts.at(x) : 0;
                    uint32_t ay = fa.spellCasts.count(y) ? fa.spellCasts.at(y) : 0;
                    uint32_t by = fb.spellCasts.count(y) ? fb.spellCasts.at(y) : 0;
                    if ((ax + bx) != (ay + by)) return (ax + bx) > (ay + by);
                    return x < y;
                });

                ImGui::Spacing();
                ImGui::TextColored(ImVec4(0.32f, 0.72f, 1.0f, 1.0f), "Fight Spells / Discs Cast");
                if (ImGui::BeginTable("##mob_compare_spell_table", 3, ImGuiTableFlags_RowBg | ImGuiTableFlags_BordersInnerH | ImGuiTableFlags_SizingStretchProp | ImGuiTableFlags_ScrollY, ImVec2(-FLT_MIN, 180.0f))) {
                    ImGui::TableSetupColumn("SPELL / DISC", ImGuiTableColumnFlags_WidthStretch, 1.8f);
                    ImGui::TableSetupColumn("Fight A Casts", ImGuiTableColumnFlags_WidthStretch, 1.0f);
                    ImGui::TableSetupColumn("Fight B Casts", ImGuiTableColumnFlags_WidthStretch, 1.0f);
                    ImGui::TableSetupScrollFreeze(0, 1);
                    ImGui::TableHeadersRow();
                    for (const auto& spellName : spellList) {
                        uint32_t ac = fa.spellCasts.count(spellName) ? fa.spellCasts.at(spellName) : 0;
                        uint32_t bc = fb.spellCasts.count(spellName) ? fb.spellCasts.at(spellName) : 0;
                        ImGui::TableNextRow();
                        ImGui::TableSetColumnIndex(0); ImGui::TextUnformatted(spellName.c_str());
                        ImGui::TableSetColumnIndex(1); ImGui::Text("%u", ac);
                        ImGui::TableSetColumnIndex(2); ImGui::Text("%u", bc);
                    }
                    if (spellList.empty()) {
                        ImGui::TableNextRow();
                        ImGui::TableSetColumnIndex(0); ImGui::TextDisabled("No spell/disc casts saved for these fights.");
                    }
                    ImGui::EndTable();
                }
            } else {
                ImGui::Spacing();
                ImGui::TextDisabled("Pick two different fights to compare.");
            }
        }
        ImGui::EndPopup();
    }

    // Open the modal from the parent/root ImGui context, not inside the child.
    if (s_requestDpsComparePopup) {
        ImGui::OpenPopup("DPS Compare##dps_compare_modal");
        s_requestDpsComparePopup = false;
    }

    ImGui::SetNextWindowSize(ImVec2(1400.0f, 900.0f), ImGuiCond_Appearing);
    ImGui::SetNextWindowSizeConstraints(ImVec2(1200.0f, 800.0f), ImVec2(FLT_MAX, FLT_MAX));
    ImGui::SetNextWindowPos(ImGui::GetMainViewport()->GetCenter(), ImGuiCond_Appearing, ImVec2(0.5f, 0.5f));
    if (ImGui::BeginPopupModal("DPS Compare##dps_compare_modal", &s_dpsComparePopupOpen, ImGuiWindowFlags_NoCollapse)) {
        auto findCompareRow = [&](const std::string& who) -> const HP_DpsCompareSnapshotRow* {
            for (const auto& r : s_compareRows) {
                if (r.name == who) return &r;
            }
            return nullptr;
        };

        if (!findCompareRow(s_compareA)) {
            s_compareA = s_compareRows.empty() ? std::string() : s_compareRows[0].name;
            s_compareReady = false;
        }
        if (!findCompareRow(s_compareB) || s_compareB == s_compareA) {
            s_compareB.clear();
            for (const auto& r : s_compareRows) {
                if (r.name != s_compareA) { s_compareB = r.name; break; }
            }
            s_compareReady = false;
        }

        ImGui::TextColored(ImVec4(0.78f, 0.42f, 1.0f, 1.0f), "Compare DPS");
        ImGui::TextDisabled("Pick two players, then press Build Compare.");
        ImGui::Separator();

        if (s_compareRows.empty()) {
            ImGui::TextDisabled("No player damage rows are available for the current fight selection.");
        } else {
            if (ImGui::BeginTable("##dps_compare_picker_table", 2, ImGuiTableFlags_SizingStretchSame | ImGuiTableFlags_BordersInnerV)) {
                ImGui::TableNextRow();
                ImGui::TableSetColumnIndex(0);
                ImGui::TextColored(ImVec4(0.32f, 0.72f, 1.0f, 1.0f), "Player A: %s", s_compareA.empty() ? "--" : s_compareA.c_str());
                if (ImGui::BeginChild("##dps_compare_a_list", ImVec2(0, 155.0f), true)) {
                    for (int i = 0; i < (int)s_compareRows.size(); ++i) {
                        const auto& r = s_compareRows[(size_t)i];
                        ImGui::PushID(10000 + i);
                        bool selected = (s_compareA == r.name);
                        if (ImGui::Selectable(r.name.c_str(), selected)) {
                            s_compareA = r.name;
                            if (s_compareB == s_compareA) s_compareB.clear();
                            s_compareReady = false;
                        }
                        ImGui::SameLine();
                        ImGui::TextDisabled("%s", HT_FormatShort(r.dmg).c_str());
                        ImGui::PopID();
                    }
                }
                ImGui::EndChild();

                ImGui::TableSetColumnIndex(1);
                ImGui::TextColored(ImVec4(0.32f, 0.72f, 1.0f, 1.0f), "Player B: %s", s_compareB.empty() ? "--" : s_compareB.c_str());
                if (ImGui::BeginChild("##dps_compare_b_list", ImVec2(0, 155.0f), true)) {
                    for (int i = 0; i < (int)s_compareRows.size(); ++i) {
                        const auto& r = s_compareRows[(size_t)i];
                        ImGui::PushID(20000 + i);
                        bool selected = (s_compareB == r.name);
                        if (ImGui::Selectable(r.name.c_str(), selected)) {
                            s_compareB = r.name;
                            if (s_compareA == s_compareB) s_compareA.clear();
                            s_compareReady = false;
                        }
                        ImGui::SameLine();
                        ImGui::TextDisabled("%s", HT_FormatShort(r.dmg).c_str());
                        ImGui::PopID();
                    }
                }
                ImGui::EndChild();
                ImGui::EndTable();
            }

            ImGui::Spacing();
            bool canCompare = !s_compareA.empty() && !s_compareB.empty() && s_compareA != s_compareB;
            if (!canCompare) ImGui::BeginDisabled();
            if (ImGui::Button("BUILD COMPARE", ImVec2(150.0f, 28.0f))) {
                // Heavy selected-fight spell/disc and melee-hit work happens only on this button.
                s_cachedCompareCasts = HP_GetSelectedDpsSpellCastsByCaster();
                buildDpsCompareMeleeBreakdown();
                s_compareReady = true;
            }
            if (!canCompare) ImGui::EndDisabled();
            ImGui::SameLine();
            if (ImGui::Button("Close", ImVec2(100.0f, 28.0f))) {
                s_dpsComparePopupOpen = false;
                ImGui::CloseCurrentPopup();
            }

            const HP_DpsCompareSnapshotRow* a = findCompareRow(s_compareA);
            const HP_DpsCompareSnapshotRow* b = findCompareRow(s_compareB);
            uint64_t aDps = (a && s_compareDur > 0) ? a->dmg / (uint64_t)s_compareDur : 0;
            uint64_t bDps = (b && s_compareDur > 0) ? b->dmg / (uint64_t)s_compareDur : 0;

            ImGui::Spacing();
            if (ImGui::BeginTable("##dps_compare_damage_table", 3, ImGuiTableFlags_RowBg | ImGuiTableFlags_BordersInnerH | ImGuiTableFlags_SizingStretchProp)) {
                ImGui::TableSetupColumn("Parse Damage", ImGuiTableColumnFlags_WidthStretch, 1.0f);
                ImGui::TableSetupColumn(s_compareA.empty() ? "Player A" : s_compareA.c_str(), ImGuiTableColumnFlags_WidthStretch, 1.0f);
                ImGui::TableSetupColumn(s_compareB.empty() ? "Player B" : s_compareB.c_str(), ImGuiTableColumnFlags_WidthStretch, 1.0f);
                ImGui::TableHeadersRow();
#define HP_CMP_DMG_ROW_POP(label, aval, bval) \
                ImGui::TableNextRow(); \
                ImGui::TableSetColumnIndex(0); ImGui::TextDisabled("%s", label); \
                ImGui::TableSetColumnIndex(1); ImGui::TextUnformatted((aval).c_str()); \
                ImGui::TableSetColumnIndex(2); ImGui::TextUnformatted((bval).c_str())
                HP_CMP_DMG_ROW_POP("Name", s_compareA.empty() ? std::string("--") : s_compareA, s_compareB.empty() ? std::string("--") : s_compareB);
                HP_CMP_DMG_ROW_POP("Total Damage", a ? HT_FormatShort(a->dmg) : std::string("--"), b ? HT_FormatShort(b->dmg) : std::string("--"));
                HP_CMP_DMG_ROW_POP("DPS", HT_FormatInteger(aDps), HT_FormatInteger(bDps));
                HP_CMP_DMG_ROW_POP("Hits", a ? HT_FormatInteger(a->hits) : std::string("--"), b ? HT_FormatInteger(b->hits) : std::string("--"));
                HP_CMP_DMG_ROW_POP("Max Hit", a ? HT_FormatInteger(a->maxHit) : std::string("--"), b ? HT_FormatInteger(b->maxHit) : std::string("--"));
                HP_CMP_DMG_ROW_POP("Melee", a ? HT_FormatShort(a->melee) : std::string("--"), b ? HT_FormatShort(b->melee) : std::string("--"));
                HP_CMP_DMG_ROW_POP("Spell", a ? HT_FormatShort(a->spell) : std::string("--"), b ? HT_FormatShort(b->spell) : std::string("--"));
                HP_CMP_DMG_ROW_POP("DoT", a ? HT_FormatShort(a->dot) : std::string("--"), b ? HT_FormatShort(b->dot) : std::string("--"));
                HP_CMP_DMG_ROW_POP("Pet / Swarm", a ? HT_FormatShort(a->pet + a->swarm) : std::string("--"), b ? HT_FormatShort(b->pet + b->swarm) : std::string("--"));
                HP_CMP_DMG_ROW_POP("Proc", a ? HT_FormatShort(a->proc) : std::string("--"), b ? HT_FormatShort(b->proc) : std::string("--"));
#undef HP_CMP_DMG_ROW_POP
                ImGui::EndTable();
            }

            ImGui::Spacing();
            ImGui::TextColored(ImVec4(1.0f, 0.78f, 0.22f, 1.0f), "Melee Hits Breakdown");
            if (s_compareReady) {
                bool hasAHitLog = !s_compareA.empty() && s_cachedCompareMeleeDetails.count(s_compareA) && !s_cachedCompareMeleeDetails[s_compareA].empty();
                bool hasBHitLog = !s_compareB.empty() && s_cachedCompareMeleeDetails.count(s_compareB) && !s_cachedCompareMeleeDetails[s_compareB].empty();
                if (!hasAHitLog) ImGui::BeginDisabled();
                std::string btnA = std::string("View ") + (s_compareA.empty() ? "Player A" : s_compareA) + " Hit Log";
                if (ImGui::Button(btnA.c_str(), ImVec2(185.0f, 24.0f))) {
                    s_meleeDetailPlayer = s_compareA;
                    s_requestMeleeDetailPopup = true;
                    s_meleeDetailPopupOpen = true;
                }
                if (!hasAHitLog) ImGui::EndDisabled();
                ImGui::SameLine();
                if (!hasBHitLog) ImGui::BeginDisabled();
                std::string btnB = std::string("View ") + (s_compareB.empty() ? "Player B" : s_compareB) + " Hit Log";
                if (ImGui::Button(btnB.c_str(), ImVec2(185.0f, 24.0f))) {
                    s_meleeDetailPlayer = s_compareB;
                    s_requestMeleeDetailPopup = true;
                    s_meleeDetailPopupOpen = true;
                }
                if (!hasBHitLog) ImGui::EndDisabled();
            }
            if (!s_compareReady) {
                ImGui::TextDisabled("Press Build Compare to load melee hit types for the selected players.");
            } else {
                auto maDmg = s_cachedCompareMeleeDmg.find(s_compareA);
                auto mbDmg = s_cachedCompareMeleeDmg.find(s_compareB);
                auto maHits = s_cachedCompareMeleeHits.find(s_compareA);
                auto mbHits = s_cachedCompareMeleeHits.find(s_compareB);

                std::unordered_set<std::string> meleeUnion;
                if (maDmg != s_cachedCompareMeleeDmg.end()) for (const auto& kv : maDmg->second) if (!kv.first.empty()) meleeUnion.insert(kv.first);
                if (mbDmg != s_cachedCompareMeleeDmg.end()) for (const auto& kv : mbDmg->second) if (!kv.first.empty()) meleeUnion.insert(kv.first);

                std::vector<std::string> meleeList(meleeUnion.begin(), meleeUnion.end());
                std::sort(meleeList.begin(), meleeList.end(), [&](const std::string& x, const std::string& y) {
                    uint64_t ax = (maDmg != s_cachedCompareMeleeDmg.end() && maDmg->second.count(x)) ? maDmg->second[x] : 0;
                    uint64_t bx = (mbDmg != s_cachedCompareMeleeDmg.end() && mbDmg->second.count(x)) ? mbDmg->second[x] : 0;
                    uint64_t ay = (maDmg != s_cachedCompareMeleeDmg.end() && maDmg->second.count(y)) ? maDmg->second[y] : 0;
                    uint64_t by = (mbDmg != s_cachedCompareMeleeDmg.end() && mbDmg->second.count(y)) ? mbDmg->second[y] : 0;
                    if ((ax + bx) != (ay + by)) return (ax + bx) > (ay + by);
                    return x < y;
                });

                std::string colADmg = s_compareA.empty() ? std::string("A DMG") : (s_compareA + " DMG");
                std::string colAHits = s_compareA.empty() ? std::string("A Hits") : (s_compareA + " Hits");
                std::string colBDmg = s_compareB.empty() ? std::string("B DMG") : (s_compareB + " DMG");
                std::string colBHits = s_compareB.empty() ? std::string("B Hits") : (s_compareB + " Hits");

                if (ImGui::BeginTable("##dps_compare_melee_hits_table", 5, ImGuiTableFlags_RowBg | ImGuiTableFlags_BordersInnerH | ImGuiTableFlags_SizingStretchProp | ImGuiTableFlags_ScrollY, ImVec2(-FLT_MIN, 185.0f))) {
                    ImGui::TableSetupColumn("MELEE HIT TYPE", ImGuiTableColumnFlags_WidthStretch, 1.4f);
                    ImGui::TableSetupColumn(colADmg.c_str(), ImGuiTableColumnFlags_WidthStretch, 1.0f);
                    ImGui::TableSetupColumn(colAHits.c_str(), ImGuiTableColumnFlags_WidthStretch, 0.75f);
                    ImGui::TableSetupColumn(colBDmg.c_str(), ImGuiTableColumnFlags_WidthStretch, 1.0f);
                    ImGui::TableSetupColumn(colBHits.c_str(), ImGuiTableColumnFlags_WidthStretch, 0.75f);
                    ImGui::TableSetupScrollFreeze(0, 1);
                    ImGui::TableHeadersRow();

                    for (const std::string& hitType : meleeList) {
                        uint64_t ad = (maDmg != s_cachedCompareMeleeDmg.end() && maDmg->second.count(hitType)) ? maDmg->second[hitType] : 0;
                        uint64_t bd = (mbDmg != s_cachedCompareMeleeDmg.end() && mbDmg->second.count(hitType)) ? mbDmg->second[hitType] : 0;
                        uint32_t ah = (maHits != s_cachedCompareMeleeHits.end() && maHits->second.count(hitType)) ? maHits->second[hitType] : 0;
                        uint32_t bh = (mbHits != s_cachedCompareMeleeHits.end() && mbHits->second.count(hitType)) ? mbHits->second[hitType] : 0;

                        ImGui::TableNextRow();
                        ImGui::TableSetColumnIndex(0); ImGui::TextUnformatted(hitType.c_str());
                        ImGui::TableSetColumnIndex(1); ImGui::TextUnformatted(ad ? HT_FormatShort(ad).c_str() : "--");
                        ImGui::TableSetColumnIndex(2); ImGui::Text("%u", ah);
                        ImGui::TableSetColumnIndex(3); ImGui::TextUnformatted(bd ? HT_FormatShort(bd).c_str() : "--");
                        ImGui::TableSetColumnIndex(4); ImGui::Text("%u", bh);
                    }

                    if (meleeList.empty()) {
                        ImGui::TableNextRow();
                        ImGui::TableSetColumnIndex(0); ImGui::TextDisabled("No melee hit-type details were found in the saved fight logs for these players.");
                    }
                    ImGui::EndTable();
                }
            }

            ImGui::Spacing();
            ImGui::TextColored(ImVec4(0.32f, 0.72f, 1.0f, 1.0f), "Spells / Discs Cast");
            if (!s_compareReady) {
                ImGui::TextDisabled("Press Build Compare to load spell/disc casts for the selected players.");
            } else {
                auto ia = s_cachedCompareCasts.find(s_compareA);
                auto ib = s_cachedCompareCasts.find(s_compareB);
                std::unordered_set<std::string> spellUnion;
                if (ia != s_cachedCompareCasts.end()) for (const auto& kv : ia->second) if (!kv.first.empty()) spellUnion.insert(kv.first);
                if (ib != s_cachedCompareCasts.end()) for (const auto& kv : ib->second) if (!kv.first.empty()) spellUnion.insert(kv.first);
                std::vector<std::string> spellList(spellUnion.begin(), spellUnion.end());
                std::sort(spellList.begin(), spellList.end(), [&](const std::string& x, const std::string& y) {
                    uint32_t ax = (ia != s_cachedCompareCasts.end() && ia->second.count(x)) ? ia->second[x] : 0;
                    uint32_t bx = (ib != s_cachedCompareCasts.end() && ib->second.count(x)) ? ib->second[x] : 0;
                    uint32_t ay = (ia != s_cachedCompareCasts.end() && ia->second.count(y)) ? ia->second[y] : 0;
                    uint32_t by = (ib != s_cachedCompareCasts.end() && ib->second.count(y)) ? ib->second[y] : 0;
                    if ((ax + bx) != (ay + by)) return (ax + bx) > (ay + by);
                    return x < y;
                });

                if (ImGui::BeginTable("##dps_compare_spells_table", 3, ImGuiTableFlags_RowBg | ImGuiTableFlags_BordersInnerH | ImGuiTableFlags_SizingStretchProp | ImGuiTableFlags_ScrollY, ImVec2(-FLT_MIN, 185.0f))) {
                    ImGui::TableSetupColumn("SPELL / DISC", ImGuiTableColumnFlags_WidthStretch, 1.8f);
                    ImGui::TableSetupColumn(s_compareA.empty() ? "Player A" : s_compareA.c_str(), ImGuiTableColumnFlags_WidthStretch, 1.0f);
                    ImGui::TableSetupColumn(s_compareB.empty() ? "Player B" : s_compareB.c_str(), ImGuiTableColumnFlags_WidthStretch, 1.0f);
                    ImGui::TableSetupScrollFreeze(0, 1);
                    ImGui::TableHeadersRow();
                    for (const auto& spellName : spellList) {
                        uint32_t ac = (ia != s_cachedCompareCasts.end() && ia->second.count(spellName)) ? ia->second[spellName] : 0;
                        uint32_t bc = (ib != s_cachedCompareCasts.end() && ib->second.count(spellName)) ? ib->second[spellName] : 0;
                        ImGui::TableNextRow();
                        ImGui::TableSetColumnIndex(0); ImGui::TextUnformatted(spellName.c_str());
                        ImGui::TableSetColumnIndex(1); ImGui::Text("%u", ac);
                        ImGui::TableSetColumnIndex(2); ImGui::Text("%u", bc);
                    }
                    if (spellList.empty()) {
                        ImGui::TableNextRow();
                        ImGui::TableSetColumnIndex(0); ImGui::TextDisabled("No spell/disc casts found for these two players in the current selection.");
                    }
                    ImGui::EndTable();
                }
            }
        }

        if (s_requestMeleeDetailPopup) {
            s_requestMeleeDetailPopup = false;
            ImGui::OpenPopup("Melee Hit Log##dps_compare_melee_detail_modal");
        }
        ImGui::SetNextWindowSize(ImVec2(720.0f, 520.0f), ImGuiCond_FirstUseEver);
        if (ImGui::BeginPopupModal("Melee Hit Log##dps_compare_melee_detail_modal", &s_meleeDetailPopupOpen, ImGuiWindowFlags_NoCollapse)) {
            const auto itDetails = s_cachedCompareMeleeDetails.find(s_meleeDetailPlayer);
            const std::vector<HP_DpsCompareMeleeDetailRow>* details = (itDetails != s_cachedCompareMeleeDetails.end()) ? &itDetails->second : nullptr;

            uint64_t totalDetailDmg = 0;
            uint64_t maxDetailHit = 0;
            if (details) {
                for (const auto& r : *details) {
                    totalDetailDmg += r.damage;
                    if (r.damage > maxDetailHit) maxDetailHit = r.damage;
                }
            }

            ImGui::TextColored(ImVec4(0.32f, 0.72f, 1.0f, 1.0f), "%s melee hits", s_meleeDetailPlayer.empty() ? "Selected player" : s_meleeDetailPlayer.c_str());
            ImGui::TextDisabled("Hits: %d   Total: %s   Max: %s",
                details ? (int)details->size() : 0,
                HT_FormatInteger(totalDetailDmg).c_str(),
                HT_FormatInteger(maxDetailHit).c_str());
            ImGui::Separator();

            if (ImGui::BeginTable("##dps_compare_melee_detail_table", 4, ImGuiTableFlags_RowBg | ImGuiTableFlags_BordersInnerH | ImGuiTableFlags_BordersOuterH | ImGuiTableFlags_SizingStretchProp | ImGuiTableFlags_ScrollY, ImVec2(-FLT_MIN, 405.0f))) {
                ImGui::TableSetupColumn("#", ImGuiTableColumnFlags_WidthFixed, 42.0f);
                ImGui::TableSetupColumn("Time", ImGuiTableColumnFlags_WidthStretch, 1.25f);
                ImGui::TableSetupColumn("Action", ImGuiTableColumnFlags_WidthStretch, 1.15f);
                ImGui::TableSetupColumn("Damage", ImGuiTableColumnFlags_WidthStretch, 0.95f);
                ImGui::TableSetupScrollFreeze(0, 1);
                ImGui::TableHeadersRow();

                if (details && !details->empty()) {
                    for (int i = 0; i < (int)details->size(); ++i) {
                        const auto& r = (*details)[(size_t)i];
                        ImGui::TableNextRow();
                        ImGui::TableSetColumnIndex(0); ImGui::Text("%d", i + 1);
                        ImGui::TableSetColumnIndex(1); ImGui::TextUnformatted(r.timeText.c_str());
                        ImGui::TableSetColumnIndex(2); ImGui::TextUnformatted(r.action.c_str());
                        ImGui::TableSetColumnIndex(3); ImGui::TextUnformatted(HT_FormatInteger(r.damage).c_str());
                    }
                } else {
                    ImGui::TableNextRow();
                    ImGui::TableSetColumnIndex(1); ImGui::TextDisabled("No individual melee hits found for this player in the saved fight logs.");
                }
                ImGui::EndTable();
            }

            if (ImGui::Button("Close", ImVec2(100.0f, 28.0f))) {
                s_meleeDetailPopupOpen = false;
                ImGui::CloseCurrentPopup();
            }
            ImGui::EndPopup();
        }

        ImGui::EndPopup();
    }

    if (openDpsTankSpikePopup)
        ImGui::OpenPopup("Spike Damage Detail##dps_tank_spike");

    ImGui::SetNextWindowSize(ImVec2(780.0f, 430.0f), ImGuiCond_Appearing);
    ImGui::SetNextWindowPos(ImGui::GetMainViewport()->GetCenter(), ImGuiCond_Appearing, ImVec2(0.5f, 0.5f));
    if (ImGui::BeginPopupModal("Spike Damage Detail##dps_tank_spike", nullptr, ImGuiWindowFlags_NoCollapse)) {
        if (s_dpsTankSpikePopupValid) {
            auto tankSpikeWallForEvent = [&](int64_t ms) -> int64_t {
                if (s_dpsTankSpikePopupWallBase > 0 && s_dpsTankSpikePopupMsBase > 0 && ms >= s_dpsTankSpikePopupMsBase)
                    return s_dpsTankSpikePopupWallBase + std::max<int64_t>(0, (ms - s_dpsTankSpikePopupMsBase) / 1000);
                return 0;
            };
            int64_t popupWallStart = tankSpikeWallForEvent(s_dpsTankSpikePopupStartMs);
            int64_t popupWallEnd = popupWallStart > 0 ? popupWallStart + 5 : 0;
            uint64_t dmgInWindow = 0;
            ImGui::TextColored(ImVec4(1.0f, 0.55f, 0.18f, 1.0f), "5 Second Spike Damage - %s", s_dpsTankSpikePopupName.c_str());
            ImGui::Separator();
            ImGui::Text("Window: %s - %s", popupWallStart > 0 ? HP_FormatTimeWithSeconds(popupWallStart).c_str() : "--:--:--", popupWallEnd > 0 ? HP_FormatTimeWithSeconds(popupWallEnd).c_str() : "--:--:--");
            if (ImGui::BeginTable("##dps_tank_spike_hits_popup", 4, ImGuiTableFlags_RowBg | ImGuiTableFlags_BordersInnerH | ImGuiTableFlags_SizingStretchProp | ImGuiTableFlags_ScrollY, ImVec2(-FLT_MIN, 170.0f))) {
                ImGui::TableSetupColumn("Time", ImGuiTableColumnFlags_WidthFixed, 100.0f);
                ImGui::TableSetupColumn("Hit By", ImGuiTableColumnFlags_WidthStretch, 1.0f);
                ImGui::TableSetupColumn("Type", ImGuiTableColumnFlags_WidthFixed, 82.0f);
                ImGui::TableSetupColumn("Damage", ImGuiTableColumnFlags_WidthFixed, 90.0f);
                ImGui::TableHeadersRow();
                for (const auto& ev : s_dpsTankSpikePopupStats.hitEvents) {
                    if (ev.ms < s_dpsTankSpikePopupStartMs || ev.ms > s_dpsTankSpikePopupEndMs) continue;
                    dmgInWindow += ev.amount;
                    ImGui::TableNextRow();
                    ImGui::TableSetColumnIndex(0); { int64_t w = tankSpikeWallForEvent(ev.ms); ImGui::TextDisabled("%s", w > 0 ? HP_FormatTimeWithSeconds(w).c_str() : "--:--:--"); }
                    ImGui::TableSetColumnIndex(1); ImGui::TextUnformatted(ev.attacker.c_str());
                    ImGui::TableSetColumnIndex(2); ImGui::TextDisabled("%s", ev.type.c_str());
                    ImGui::TableSetColumnIndex(3); ImGui::Text("%s", HT_FormatInteger(ev.amount).c_str());
                }
                ImGui::EndTable();
            }
            ImGui::Text("Damage Taken: %s", HT_FormatInteger(dmgInWindow).c_str());
            ImGui::Spacing();
            ImGui::TextColored(ImVec4(0.35f, 1.0f, 0.42f, 1.0f), "Heals in same 5 seconds");
            std::vector<LiveHealDetailRow> healsForSpike;
            if (popupWallStart > 0) {
                if (tankSelectedFightIndex >= 0) {
                    std::lock_guard<std::mutex> hk(g_completedHealFightsMutex);
                    if (tankSelectedFightIndex < (int)g_completedHealFights.size()) {
                        for (const auto& h : g_completedHealFights[(size_t)tankSelectedFightIndex].details)
                            if (HP_SameNameNoCase(h.target, s_dpsTankSpikePopupName) && h.wall >= popupWallStart && h.wall <= popupWallEnd)
                                healsForSpike.push_back(h);
                    }
                } else {
                    std::lock_guard<std::mutex> hk(g_liveHealsMutex);
                    for (const auto& h : g_liveHeals.details)
                        if (HP_SameNameNoCase(h.target, s_dpsTankSpikePopupName) && h.wall >= popupWallStart && h.wall <= popupWallEnd)
                            healsForSpike.push_back(h);
                }
            }
            if (ImGui::BeginTable("##dps_tank_spike_heals_popup", 4, ImGuiTableFlags_RowBg | ImGuiTableFlags_BordersInnerH | ImGuiTableFlags_SizingStretchProp | ImGuiTableFlags_ScrollY, ImVec2(-FLT_MIN, 130.0f))) {
                ImGui::TableSetupColumn("Time", ImGuiTableColumnFlags_WidthFixed, 100.0f);
                ImGui::TableSetupColumn("Healed By", ImGuiTableColumnFlags_WidthStretch, 1.0f);
                ImGui::TableSetupColumn("Spell", ImGuiTableColumnFlags_WidthStretch, 1.0f);
                ImGui::TableSetupColumn("Amount", ImGuiTableColumnFlags_WidthFixed, 90.0f);
                ImGui::TableHeadersRow();
                for (const auto& h : healsForSpike) {
                    ImGui::TableNextRow();
                    ImGui::TableSetColumnIndex(0); ImGui::TextDisabled("%s", HP_FormatTimeWithSeconds(h.wall).c_str());
                    ImGui::TableSetColumnIndex(1); { std::string hc = HP_NormalizeHealCasterName(h.caster); ImGui::TextColored(ImVec4(0.35f, 1.0f, 0.42f, 1.0f), "%s", hc.c_str()); }
                    ImGui::TableSetColumnIndex(2); ImGui::TextUnformatted(h.name.c_str());
                    ImGui::TableSetColumnIndex(3); ImGui::Text("%s", HT_FormatInteger(h.amount).c_str());
                }
                if (healsForSpike.empty()) {
                    ImGui::TableNextRow();
                    ImGui::TableSetColumnIndex(1); ImGui::TextDisabled("No heals landed during this spike window.");
                }
                ImGui::EndTable();
            }
        }
        ImGui::Spacing();
        if (ImGui::Button("Close", ImVec2(100.0f, 28.0f))) ImGui::CloseCurrentPopup();
        ImGui::EndPopup();
    }

    if (openDpsTankPopup)
        ImGui::OpenPopup("Tank Stats Detail##dps_right_tank");

    ImGui::SetNextWindowSize(ImVec2(1180.0f, 390.0f), ImGuiCond_Appearing);
    ImGui::SetNextWindowPos(ImGui::GetMainViewport()->GetCenter(), ImGuiCond_Appearing, ImVec2(0.5f, 0.5f));
    if (ImGui::BeginPopupModal("Tank Stats Detail##dps_right_tank", nullptr, ImGuiWindowFlags_NoCollapse)) {
        if (s_dpsTankPopupValid) {
            const LiveTankRow& t = s_dpsTankPopupStats;
            const uint64_t swings = HP_TankSwings(t);
            const uint32_t avoided = HP_TankAvoided(t);
            auto pct = [](uint64_t n, uint64_t d) -> double { return d ? ((double)n * 100.0 / (double)d) : 0.0; };
            auto tankWallForEvent = [&](int64_t ms) -> int64_t {
                if (s_dpsTankPopupWallBase > 0 && s_dpsTankPopupMsBase > 0 && ms >= s_dpsTankPopupMsBase)
                    return s_dpsTankPopupWallBase + std::max<int64_t>(0, (ms - s_dpsTankPopupMsBase) / 1000);
                return HP_WallNow();
            };

            ImGui::TextColored(ImVec4(1.0f, 0.55f, 0.18f, 1.0f), "Tank Stats - %s", s_dpsTankPopupName.c_str());
            ImGui::Separator();
            ImGui::Text("Total Damage: %s", HT_FormatInteger(t.damage).c_str());
            ImGui::SameLine(210.0f); ImGui::Text("Swings: %s", HT_FormatInteger(swings).c_str());
            ImGui::SameLine(360.0f); ImGui::Text("Max Hit: %s", HT_FormatInteger(t.maxHit).c_str());
            ImGui::Text("Avoided: %u (%.2f%%)", avoided, pct(avoided, swings));
            ImGui::SameLine(210.0f); ImGui::Text("Worst 3s Spike: %s", HT_FormatInteger(HP_TankWorstSpike3s(t)).c_str());
            ImGui::Spacing();

            struct HP_TankTypeSummary { std::string type; uint64_t damage = 0; uint32_t hits = 0; uint32_t maxHit = 0; };
            std::unordered_map<std::string, HP_TankTypeSummary> byType;
            for (const auto& ev : t.hitEvents) {
                std::string typ = ev.type.empty() ? std::string("Hit") : ev.type;
                std::string key = LowerCopy(typ);
                if (key == "hit" || key == "melee") typ = "Total Melee";
                else if (key == "nonmelee" || key == "non-melee") typ = "Non-Melee";
                else if (key == "dot") typ = "DoT";
                auto& row = byType[typ];
                row.type = typ;
                row.damage += ev.amount;
                row.hits += 1;
                if (ev.amount > row.maxHit) row.maxHit = ev.amount;
            }
            std::vector<HP_TankTypeSummary> typeRows;
            HP_TankTypeSummary totalRow;
            totalRow.type = "Total Melee";
            totalRow.damage = t.damage;
            totalRow.hits = t.hits;
            totalRow.maxHit = t.maxHit;
            typeRows.push_back(totalRow);
            for (const auto& kv : byType) {
                if (kv.first == "Total Melee") continue;
                typeRows.push_back(kv.second);
            }
            std::sort(typeRows.begin() + (typeRows.size() > 1 ? 1 : 0), typeRows.end(), [](const HP_TankTypeSummary& a, const HP_TankTypeSummary& b) {
                if (a.damage != b.damage) return a.damage > b.damage;
                return a.type < b.type;
            });

            if (ImGui::BeginTable("##dps_tank_stats_summary", 16, ImGuiTableFlags_RowBg | ImGuiTableFlags_BordersInnerH | ImGuiTableFlags_BordersOuter | ImGuiTableFlags_SizingStretchSame, ImVec2(-FLT_MIN, 185.0f))) {
                ImGui::TableSetupColumn("Type");
                ImGui::TableSetupColumn("Dmg");
                ImGui::TableSetupColumn("Avg");
                ImGui::TableSetupColumn("Att");
                ImGui::TableSetupColumn("Inv");
                ImGui::TableSetupColumn("Rip");
                ImGui::TableSetupColumn("Par");
                ImGui::TableSetupColumn("Dod");
                ImGui::TableSetupColumn("Blk");
                ImGui::TableSetupColumn("Miss");
                ImGui::TableSetupColumn("Def%");
                ImGui::TableSetupColumn("Hit%");
                ImGui::TableSetupColumn("Hits");
                ImGui::TableSetupColumn("Abs");
                ImGui::TableSetupColumn("Max");
                ImGui::TableSetupColumn("Real");
                ImGui::TableHeadersRow();
                for (size_t i = 0; i < typeRows.size(); ++i) {
                    const auto& r = typeRows[i];
                    const bool isTotal = (i == 0);
                    const uint64_t attempts = isTotal ? swings : r.hits;
                    const uint32_t rip = isTotal ? t.ripostes : 0;
                    const uint32_t par = isTotal ? t.parries : 0;
                    const uint32_t dod = isTotal ? t.dodges : 0;
                    const uint32_t blk = isTotal ? t.blocks : 0;
                    const uint32_t mis = isTotal ? t.misses : 0;
                    const uint32_t def = isTotal ? avoided : 0;
                    const uint64_t avg = r.hits ? (r.damage / r.hits) : 0;
                    ImGui::TableNextRow();
                    int c = 0;
                    ImGui::TableSetColumnIndex(c++); ImGui::TextUnformatted(r.type.c_str());
                    ImGui::TableSetColumnIndex(c++); ImGui::Text("%s", HT_FormatInteger(r.damage).c_str());
                    ImGui::TableSetColumnIndex(c++); ImGui::Text("%s", HT_FormatInteger(avg).c_str());
                    ImGui::TableSetColumnIndex(c++); ImGui::Text("%s", HT_FormatInteger(attempts).c_str());
                    ImGui::TableSetColumnIndex(c++); ImGui::TextUnformatted("0");
                    ImGui::TableSetColumnIndex(c++); ImGui::Text("%u", rip);
                    ImGui::TableSetColumnIndex(c++); ImGui::Text("%u", par);
                    ImGui::TableSetColumnIndex(c++); ImGui::Text("%u", dod);
                    ImGui::TableSetColumnIndex(c++); ImGui::Text("%u", blk);
                    ImGui::TableSetColumnIndex(c++); ImGui::Text("%u", mis);
                    ImGui::TableSetColumnIndex(c++); ImGui::Text("%.1f", pct(def, attempts));
                    ImGui::TableSetColumnIndex(c++); ImGui::Text("%.1f", pct(r.hits, attempts));
                    ImGui::TableSetColumnIndex(c++); ImGui::Text("%u", r.hits);
                    ImGui::TableSetColumnIndex(c++); ImGui::TextUnformatted("0");
                    ImGui::TableSetColumnIndex(c++); ImGui::Text("%s", HT_FormatInteger(r.maxHit).c_str());
                    ImGui::TableSetColumnIndex(c++); ImGui::Text("%u", r.hits);
                }
                ImGui::EndTable();
            }

            ImGui::Spacing();
            ImGui::TextDisabled("Incoming hit log removed. This popup now shows tanking stats only.");
        }
        ImGui::Spacing();
        if (ImGui::Button("Close", ImVec2(100.0f, 28.0f))) ImGui::CloseCurrentPopup();
        ImGui::EndPopup();
    }

    ImGui::EndChild();

    ImGui::PopStyleColor(2);
    ImGui::EndChild();
}

static void HP_DrawHealsPage(float leftW, float rightW)
{
    struct HealUiRow { std::string name; uint64_t total = 0; uint32_t count = 0; uint32_t maxHeal = 0; };
    auto makeRows = [](const std::unordered_map<std::string, LiveHealRow>& src) {
        std::vector<HealUiRow> out;
        out.reserve(src.size());
        for (const auto& kv : src) {
            if (kv.first.empty() || kv.second.total == 0) continue;
            out.push_back({ kv.first, kv.second.total, kv.second.count, kv.second.maxHeal });
        }
        std::sort(out.begin(), out.end(), [](const HealUiRow& a, const HealUiRow& b) { return a.total > b.total; });
        return out;
    };

    std::vector<HealUiRow> healerRows;
    std::vector<HealUiRow> targetRows;
    std::vector<HealUiRow> spellRows;
    std::vector<LiveHealDetailRow> detailRows;
    uint64_t totalHealing = 0;
    uint32_t totalHeals = 0;
    uint32_t maxHeal = 0;
    int64_t now = NowMs();
    int dur = 0;

    int selectedFightForHeader = g_fullUiDpsSelectedFight.load();
    const bool combiningSelectedFights = !g_dpsSelectedFights.empty();
    int combinedHealFightCount = 0;
    {
        LiveHealFight hf;
        bool haveArchived = false;

        // Match the DPS tab behavior: when SELECT ALL or multi-select is active,
        // the Heals tab must combine healing data for every selected fight instead
        // of showing only the single highlighted fight.  The fight list selection
        // is shared between DPS / Heals / Spells / Tank, so use g_dpsSelectedFights
        // as the common multi-selection source.
        if (combiningSelectedFights) {
            int64_t minStart = 0;
            int64_t maxEnd = 0;

            std::lock_guard<std::mutex> hk(g_completedHealFightsMutex);
            for (int idx : g_dpsSelectedFights) {
                if (idx < 0 || idx >= (int)g_completedHealFights.size()) continue;
                const LiveHealFight& src = g_completedHealFights[(size_t)idx];

                if (hf.mob.empty()) hf.mob = "Selected Healing";
                if (src.startedMs > 0 && (minStart == 0 || src.startedMs < minStart)) minStart = src.startedMs;
                if (src.lastHealMs > maxEnd) maxEnd = src.lastHealMs;

                hf.total += src.total;
                for (const auto& kv : src.healers) {
                    LiveHealRow& dst = hf.healers[kv.first];
                    dst.total += kv.second.total;
                    dst.count += kv.second.count;
                    if (kv.second.maxHeal > dst.maxHeal) dst.maxHeal = kv.second.maxHeal;
                }
                for (const auto& kv : src.targets) {
                    LiveHealRow& dst = hf.targets[kv.first];
                    dst.total += kv.second.total;
                    dst.count += kv.second.count;
                    if (kv.second.maxHeal > dst.maxHeal) dst.maxHeal = kv.second.maxHeal;
                }
                for (const auto& kv : src.spells) {
                    LiveHealRow& dst = hf.spells[kv.first];
                    dst.total += kv.second.total;
                    dst.count += kv.second.count;
                    if (kv.second.maxHeal > dst.maxHeal) dst.maxHeal = kv.second.maxHeal;
                }
                hf.details.insert(hf.details.end(), src.details.begin(), src.details.end());
                ++combinedHealFightCount;
            }

            hf.startedMs = minStart;
            hf.lastHealMs = maxEnd;
            haveArchived = true;
        } else if (selectedFightForHeader >= 0) {
            std::lock_guard<std::mutex> hk(g_completedHealFightsMutex);
            if (selectedFightForHeader < (int)g_completedHealFights.size()) {
                hf = g_completedHealFights[(size_t)selectedFightForHeader];
                haveArchived = true;
            }
        }
        if (!haveArchived) {
            if (selectedFightForHeader < 0) {
                std::lock_guard<std::mutex> lk(g_liveHealsMutex);
                hf = g_liveHeals;
            } else {
                // A completed DPS fight with no matching saved healing data should
                // show empty healing stats, not the newest live/last fight heals.
                hf = LiveHealFight{};
            }
        }

        totalHealing = hf.total;
        if (hf.startedMs) {
            int64_t durEnd = (combiningSelectedFights || selectedFightForHeader >= 0 || (now - hf.lastHealMs) > kLiveDpsTimeoutMs) ? hf.lastHealMs : now;
            dur = (int)std::max<int64_t>(1, (durEnd - hf.startedMs) / 1000);
        } else {
            dur = 0;
        }
        healerRows = makeRows(hf.healers);
        targetRows = makeRows(hf.targets);
        spellRows = makeRows(hf.spells);
        detailRows = hf.details;
        for (const auto& r : healerRows) {
            totalHeals += r.count;
            if (r.maxHeal > maxHeal) maxHeal = r.maxHeal;
        }
    }

    uint64_t raidHps = dur > 0 ? totalHealing / (uint64_t)std::max(1, dur) : 0;
    uint64_t avgHeal = totalHeals ? totalHealing / (uint64_t)totalHeals : 0;

    std::string fightTitle = "Current Healing";
    std::string fightDateText = "Live Heals";
    int playersForHeader = (int)healerRows.size();
    if (combiningSelectedFights) {
        int dpsFightCount = 0;
        int64_t minStart = 0;
        int64_t maxEnd = 0;
        int64_t maxWall = 0;
        std::unordered_set<std::string> players;
        {
            std::lock_guard<std::mutex> hk(g_completedDpsMutex);
            for (int idx : g_dpsSelectedFights) {
                if (idx < 0 || idx >= (int)g_completedDpsFights.size()) continue;
                const auto& f = g_completedDpsFights[(size_t)idx];
                if (f.startedMs > 0 && (minStart == 0 || f.startedMs < minStart)) minStart = f.startedMs;
                if (f.endedMs > maxEnd) maxEnd = f.endedMs;
                if (f.wallEnded > maxWall) maxWall = f.wallEnded;
                for (const auto& kv : f.players) players.insert(HP_GetPetCombinedDisplayName(kv.first));
                ++dpsFightCount;
            }
        }
        if (dpsFightCount > 0) {
            fightTitle = std::to_string(dpsFightCount) + " selected fights";
            fightDateText = maxWall > 0 ? HP_FormatDateTimeLong(maxWall) : "Combined Healing";
            if (dur <= 0 && minStart > 0 && maxEnd > minStart) dur = (int)std::max<int64_t>(1, (maxEnd - minStart) / 1000);
            playersForHeader = std::max(playersForHeader, (int)players.size());
        } else if (combinedHealFightCount > 0) {
            fightTitle = std::to_string(combinedHealFightCount) + " selected fights";
            fightDateText = "Combined Healing";
        }
    } else if (selectedFightForHeader >= 0) {
        std::lock_guard<std::mutex> hk(g_completedDpsMutex);
        if (selectedFightForHeader < (int)g_completedDpsFights.size()) {
            const auto& hf = g_completedDpsFights[(size_t)selectedFightForHeader];
            fightTitle = hf.mob;
            fightDateText = HP_FormatDateTimeLong(hf.wallEnded > 0 ? hf.wallEnded : hf.wallStarted);
            if (dur <= 0) dur = (int)std::max<int64_t>(1, (hf.endedMs - hf.startedMs) / 1000);
            playersForHeader = std::max(playersForHeader, (int)hf.players.size());
        }
    } else {
        std::lock_guard<std::mutex> dlk(g_liveDpsMutex);
        if (!g_liveDps.mob.empty()) {
            fightTitle = g_liveDps.mob;
            fightDateText = "Live Fight";
            if (dur <= 0 && g_liveDps.startedMs) dur = (int)std::max<int64_t>(1, (now - g_liveDps.startedMs) / 1000);
            playersForHeader = std::max(playersForHeader, (int)g_liveDps.players.size());
        }
    }

    uint64_t directHeal = 0, hotRegen = 0, runeGlyph = 0, shieldHeal = 0, procHeal = 0, otherHeal = 0;
    for (const auto& r : spellRows) {
        std::string n = LowerCopy(r.name);
        if (n.find("rune") != std::string::npos || n.find("glyph") != std::string::npos || n.find("aspect of survival") != std::string::npos) runeGlyph += r.total;
        else if (n.find("shield") != std::string::npos) shieldHeal += r.total;
        else if (n.find("proc") != std::string::npos) procHeal += r.total;
        else if (HP_IsHotRegenHealName(r.name)) hotRegen += r.total;
        else if (n.find("direct") != std::string::npos) directHeal += r.total;
        else otherHeal += r.total;
    }

    ImGui::BeginChild("##heals_main_futuristic", ImVec2(leftW, 0), true);

    ImDrawList* dl = ImGui::GetWindowDrawList();
    ImVec2 headerPos = ImGui::GetCursorScreenPos();
    float headerW = ImGui::GetContentRegionAvail().x;
    dl->AddRectFilled(headerPos, ImVec2(headerPos.x + headerW, headerPos.y + 78.0f), IM_COL32(6, 12, 25, 215), 10.0f);
    dl->AddRect(headerPos, ImVec2(headerPos.x + headerW, headerPos.y + 78.0f), IM_COL32(70, 200, 100, 130), 10.0f, 0, 1.0f);
    HP_DrawDemonIconInList(dl, ImVec2(headerPos.x + 16.0f, headerPos.y + 15.0f), 46.0f);
    ImGui::SetCursorScreenPos(ImVec2(headerPos.x + 74.0f, headerPos.y + 12.0f));
    ImGui::PushStyleColor(ImGuiCol_Text, IM_COL32(235, 245, 255, 255));
    ImGui::Text("%s", fightTitle.c_str());
    ImGui::PopStyleColor();
    ImGui::SetCursorScreenPos(ImVec2(headerPos.x + 74.0f, headerPos.y + 43.0f));
    ImGui::TextDisabled("%s  •  Duration: %02d:%02d  •  Players: %d", fightDateText.c_str(), dur / 60, dur % 60, playersForHeader);
    ImGui::SetCursorScreenPos(ImVec2(headerPos.x + headerW - 158.0f, headerPos.y + 14.0f));
    ImGui::Button("COPY", ImVec2(64.0f, 28.0f));
    ImGui::SameLine();
    ImGui::Button("EXPORT", ImVec2(80.0f, 28.0f));
    ImGui::SetCursorScreenPos(ImVec2(headerPos.x, headerPos.y + 86.0f));

    {
        ImVec2 cardsStart = ImGui::GetCursorScreenPos();
        float avail = ImGui::GetContentRegionAvail().x;
        const float gap = 8.0f;
        float cardW = std::max(130.0f, (avail - gap * 3.0f) / 4.0f);
        struct StatCardDef { const char* title; std::string value; const char* sub; ImU32 accent; } cards[4] = {
            { "TOTAL HEALING", HT_FormatShort(totalHealing), "", IM_COL32(105, 235, 100, 255) },
            { "HEALS", HT_FormatInteger(totalHeals), "", IM_COL32(105, 235, 100, 255) },
            { "AVERAGE HEAL", HT_FormatInteger(avgHeal), "", IM_COL32(105, 235, 100, 255) },
            { "MAX HEAL", HT_FormatInteger(maxHeal), "", IM_COL32(105, 235, 100, 255) }
        };
        for (int ci = 0; ci < 4; ++ci) {
            ImGui::SetCursorScreenPos(ImVec2(cardsStart.x + (cardW + gap) * ci, cardsStart.y));
            HP_DrawDpsHeroStat(cards[ci].title, cards[ci].value.c_str(), cards[ci].sub, cards[ci].accent, cardW);
        }
        ImGui::SetCursorScreenPos(ImVec2(cardsStart.x, cardsStart.y + 74.0f));
    }

    ImGui::Spacing();
    float upperH = 220.0f;
    float availW = ImGui::GetContentRegionAvail().x;
    // Match the DPS tab layout: large graph panel on the left, breakdown panel on the right.
    float graphW = std::max(520.0f, (availW - 8.0f) * 0.58f);

    std::vector<HP_DpsUiRow> graphRows;
    graphRows.reserve(healerRows.size());
    for (const auto& r : healerRows) { HP_DpsUiRow gr; gr.name = r.name; gr.dmg = r.total; gr.hits = r.count; gr.maxHit = r.maxHeal; graphRows.push_back(gr); }

    ImGui::BeginChild("##heals_graph_panel", ImVec2(graphW, upperH), true);
    ImGui::TextColored(ImVec4(0.32f, 0.90f, 0.45f, 1.0f), "HEALING OVER TIME");
    HP_DrawDpsMiniGraph(graphRows, totalHealing, ImGui::GetContentRegionAvail().x, 174.0f, dur, "HPS");
    ImGui::EndChild();
    ImGui::SameLine();

    ImGui::BeginChild("##heals_type_panel", ImVec2(0, upperH), true);
    ImGui::TextColored(ImVec4(0.32f, 0.90f, 0.45f, 1.0f), "HEALING BREAKDOWN BY TYPE");
    HP_DrawDpsDonutFallback(directHeal, hotRegen, runeGlyph, shieldHeal + procHeal, otherHeal, totalHealing, 120.0f);
    ImGui::SameLine();
    ImGui::BeginGroup();
    HP_DrawDpsTypeBar("Direct Heal", directHeal, totalHealing, IM_COL32(105, 220, 110, 255), 128.0f);
    HP_DrawDpsTypeBar("HoT / Regen", hotRegen, totalHealing, IM_COL32(60, 170, 255, 255), 128.0f);
    HP_DrawDpsTypeBar("Rune / Glyph", runeGlyph, totalHealing, IM_COL32(255, 190, 60, 255), 128.0f);
    HP_DrawDpsTypeBar("Proc / Shield", shieldHeal + procHeal, totalHealing, IM_COL32(170, 90, 255, 255), 128.0f);
    ImGui::EndGroup();
    ImGui::EndChild();

    ImGui::Spacing();
    float midH = std::max(210.0f, (ImGui::GetContentRegionAvail().y - 210.0f) * 0.50f);

    ImGui::BeginChild("##healers_panel", ImVec2(0, midH), true);
    ImGui::TextColored(ImVec4(0.32f, 0.90f, 0.45f, 1.0f), "HEALERS");
    if (ImGui::BeginTable("##healers_table_future", 8, ImGuiTableFlags_RowBg | ImGuiTableFlags_BordersInnerH | ImGuiTableFlags_SizingStretchProp | ImGuiTableFlags_ScrollY, ImVec2(0, ImGui::GetContentRegionAvail().y))) {
        ImGui::TableSetupColumn("#", ImGuiTableColumnFlags_WidthFixed, 26);
        ImGui::TableSetupColumn("Player", ImGuiTableColumnFlags_WidthStretch, 1.55f);
        ImGui::TableSetupColumn("Class", ImGuiTableColumnFlags_WidthFixed, 68);
        ImGui::TableSetupColumn("Total Healing", ImGuiTableColumnFlags_WidthFixed, 120);
        ImGui::TableSetupColumn("HPS", ImGuiTableColumnFlags_WidthFixed, 82);
        ImGui::TableSetupColumn("%", ImGuiTableColumnFlags_WidthFixed, 50);
        ImGui::TableSetupColumn("Heals", ImGuiTableColumnFlags_WidthFixed, 56);
        ImGui::TableSetupColumn("Max", ImGuiTableColumnFlags_WidthFixed, 72);
        ImGui::TableHeadersRow();
        int idx = 0;
        for (const auto& r : healerRows) {
            double pct = totalHealing ? (double)r.total * 100.0 / (double)totalHealing : 0.0;
            ImGui::TableNextRow(ImGuiTableRowFlags_None, 24.0f);
            ImGui::TableSetColumnIndex(0); ImGui::Text("%d", ++idx);
            ImGui::TableSetColumnIndex(1); ImGui::TextColored(ImVec4(0.35f, 1.0f, 0.35f, 1.0f), "%s", r.name.c_str());
            ImGui::TableSetColumnIndex(2);
            std::string cls = HP_GetPlayerClassName(r.name);
            HP_IconTexture* classIcon = HP_GetClassIconTexture(cls);
            if (classIcon && classIcon->id) { ImVec2 cp = ImGui::GetCursorScreenPos(); ImGui::GetWindowDrawList()->AddImage(classIcon->id, cp, ImVec2(cp.x + 22.0f, cp.y + 22.0f)); ImGui::SetCursorScreenPos(ImVec2(cp.x + 26.0f, cp.y + 2.0f)); }
            ImGui::TextDisabled("%s", cls.c_str());
            ImGui::TableSetColumnIndex(3); ImGui::Text("%s", HT_FormatShort(r.total).c_str());
            ImGui::TableSetColumnIndex(4); ImGui::Text("%s", HT_FormatInteger(dur ? r.total / (uint64_t)dur : 0).c_str());
            ImGui::TableSetColumnIndex(5); ImGui::Text("%.1f", pct);
            ImGui::TableSetColumnIndex(6); ImGui::Text("%u", r.count);
            ImGui::TableSetColumnIndex(7); ImGui::Text("%u", r.maxHeal);
        }
        ImGui::TableNextRow();
        ImGui::TableSetColumnIndex(1); ImGui::TextDisabled("TOTAL");
        ImGui::TableSetColumnIndex(3); ImGui::TextDisabled("%s", HT_FormatShort(totalHealing).c_str());
        ImGui::TableSetColumnIndex(4); ImGui::TextDisabled("%s", HT_FormatInteger(raidHps).c_str());
        ImGui::TableSetColumnIndex(5); ImGui::TextDisabled("100%%");
        ImGui::TableSetColumnIndex(6); ImGui::TextDisabled("%u", totalHeals);
        ImGui::TableSetColumnIndex(7); ImGui::TextDisabled("%u", maxHeal);
        ImGui::EndTable();
    }
    ImGui::EndChild();

    ImGui::Spacing();
    float bottomH = ImGui::GetContentRegionAvail().y;
    float thirdW = std::max(260.0f, (ImGui::GetContentRegionAvail().x - 16.0f) / 3.0f);

    ImGui::BeginChild("##healing_spell_panel", ImVec2(thirdW, bottomH), true);
    ImGui::TextColored(ImVec4(0.32f, 0.90f, 0.45f, 1.0f), "HEALING BY SPELL (Top 10)");
    if (ImGui::BeginTable("##healing_spell_table_future", 6, ImGuiTableFlags_RowBg | ImGuiTableFlags_BordersInnerH | ImGuiTableFlags_SizingStretchProp | ImGuiTableFlags_ScrollY, ImVec2(0, ImGui::GetContentRegionAvail().y))) {
        ImGui::TableSetupColumn("#", ImGuiTableColumnFlags_WidthFixed, 26);
        ImGui::TableSetupColumn("Spell", ImGuiTableColumnFlags_WidthStretch, 2.2f);
        ImGui::TableSetupColumn("Total", ImGuiTableColumnFlags_WidthFixed, 58);
        ImGui::TableSetupColumn("%", ImGuiTableColumnFlags_WidthFixed, 40);
        ImGui::TableSetupColumn("Heals", ImGuiTableColumnFlags_WidthFixed, 44);
        ImGui::TableSetupColumn("Max", ImGuiTableColumnFlags_WidthFixed, 54);
        ImGui::TableHeadersRow();
        int idx = 0;
        for (const auto& r : spellRows) {
            if (idx >= 10) break;
            double pct = totalHealing ? (double)r.total * 100.0 / (double)totalHealing : 0.0;
            ImGui::TableNextRow(ImGuiTableRowFlags_None, 24.0f);
            ImGui::TableSetColumnIndex(0); ImGui::Text("%d", ++idx);
            ImGui::TableSetColumnIndex(1); ImGui::Text("%s", r.name.c_str());
            ImGui::TableSetColumnIndex(2); ImGui::Text("%s", HT_FormatShort(r.total).c_str());
            ImGui::TableSetColumnIndex(3); ImGui::Text("%.1f%%", pct);
            ImGui::TableSetColumnIndex(4); ImGui::Text("%u", r.count);
            ImGui::TableSetColumnIndex(5); ImGui::Text("%s", HT_FormatShort(r.maxHeal).c_str());
        }
        if (idx == 0) { ImGui::TableNextRow(); ImGui::TableSetColumnIndex(1); ImGui::TextDisabled("No healing spells yet."); }
        ImGui::EndTable();
    }
    ImGui::EndChild();
    ImGui::SameLine();

    ImGui::BeginChild("##healing_target_table_panel", ImVec2(thirdW, bottomH), true);
    ImGui::TextColored(ImVec4(0.32f, 0.90f, 0.45f, 1.0f), "HEALED FOR (Top 10)");
    std::unordered_map<std::string, std::unordered_map<std::string, uint64_t>> healedByMap;
    for (const auto& d : detailRows) {
        if (d.target.empty() || d.caster.empty()) continue;
        healedByMap[d.target][d.caster] += d.amount;
    }
    auto fmtHealedBy = [&](const std::string& target) -> std::string {
        std::vector<std::pair<std::string, uint64_t>> v;
        auto it = healedByMap.find(target);
        if (it != healedByMap.end()) {
            for (const auto& kv : it->second) v.push_back(kv);
            std::sort(v.begin(), v.end(), [](const auto& a, const auto& b){ return a.second > b.second; });
        }
        std::string out;
        int n = 0;
        for (const auto& kv : v) {
            if (n++ >= 3) { out += ", +" + std::to_string((int)v.size() - 3); break; }
            if (!out.empty()) out += ", ";
            out += kv.first + " " + HT_FormatShort(kv.second);
        }
        return out.empty() ? "-" : out;
    };
    if (ImGui::BeginTable("##healed_for_table_future", 6, ImGuiTableFlags_RowBg | ImGuiTableFlags_BordersInnerH | ImGuiTableFlags_SizingStretchProp | ImGuiTableFlags_ScrollY, ImVec2(0, ImGui::GetContentRegionAvail().y))) {
        ImGui::TableSetupColumn("#", ImGuiTableColumnFlags_WidthFixed, 26);
        ImGui::TableSetupColumn("Player", ImGuiTableColumnFlags_WidthStretch, 2.2f);
        ImGui::TableSetupColumn("Total", ImGuiTableColumnFlags_WidthFixed, 58);
        ImGui::TableSetupColumn("%", ImGuiTableColumnFlags_WidthFixed, 40);
        ImGui::TableSetupColumn("Heals", ImGuiTableColumnFlags_WidthFixed, 44);
        ImGui::TableSetupColumn("Max", ImGuiTableColumnFlags_WidthFixed, 54);
        ImGui::TableHeadersRow();
        int idx = 0;
        for (const auto& r : targetRows) {
            if (idx >= 10) break;
            double pct = totalHealing ? (double)r.total * 100.0 / (double)totalHealing : 0.0;
            ImGui::TableNextRow(ImGuiTableRowFlags_None, 24.0f);
            ImGui::TableSetColumnIndex(0); ImGui::Text("%d", ++idx);
            ImGui::TableSetColumnIndex(1);
            ImGui::PushStyleColor(ImGuiCol_Text, ImVec4(0.25f, 0.85f, 1.0f, 1.0f));
            if (ImGui::Selectable(r.name.c_str(), false, ImGuiSelectableFlags_SpanAllColumns | ImGuiSelectableFlags_AllowItemOverlap)) {
                ImGui::OpenPopup((std::string("HealedByPopup##") + r.name).c_str());
            }
            if (ImGui::IsItemHovered()) {
                ImGui::BeginTooltip();
                ImGui::TextUnformatted("Click to see who healed this player and for how much.");
                ImGui::EndTooltip();
            }
            ImGui::PopStyleColor();
            if (ImGui::BeginPopup((std::string("HealedByPopup##") + r.name).c_str())) {
                ImGui::TextColored(ImVec4(0.32f, 0.90f, 0.45f, 1.0f), "%s was healed by", r.name.c_str());
                ImGui::Separator();
                std::vector<std::pair<std::string, uint64_t>> v;
                auto it = healedByMap.find(r.name);
                if (it != healedByMap.end()) {
                    for (const auto& kv : it->second) v.push_back(kv);
                    std::sort(v.begin(), v.end(), [](const auto& a, const auto& b){ return a.second > b.second; });
                }
                for (const auto& kv : v) {
                    ImGui::Text("%s", kv.first.c_str());
                    ImGui::SameLine(180.0f);
                    ImGui::Text("%s", HT_FormatShort(kv.second).c_str());
                }
                if (v.empty()) ImGui::TextDisabled("No healer detail for this target.");
                ImGui::EndPopup();
            }
            ImGui::TableSetColumnIndex(2); ImGui::Text("%s", HT_FormatShort(r.total).c_str());
            ImGui::TableSetColumnIndex(3); ImGui::Text("%.1f", pct);
            ImGui::TableSetColumnIndex(4); ImGui::Text("%u", r.count);
            ImGui::TableSetColumnIndex(5); ImGui::Text("%s", HT_FormatShort(r.maxHeal).c_str());
        }
        if (idx == 0) { ImGui::TableNextRow(); ImGui::TableSetColumnIndex(1); ImGui::TextDisabled("No healed target data yet."); }
        ImGui::EndTable();
    }
    ImGui::EndChild();
    ImGui::SameLine();

    struct HealDetailAggRow {
        std::string type, name, caster, target;
        uint64_t total = 0;
        uint32_t count = 0;
        uint32_t maxAmount = 0;
        int64_t lastWall = 0;
    };
    std::vector<HealDetailAggRow> detailAggRows;
    {
        std::unordered_map<std::string, HealDetailAggRow> agg;
        for (const auto& d : detailRows) {
            if (!(HP_IsRuneOrProcHealName(d.name) || HP_IsRuneOrProcHealName(d.type))) continue;
            std::string key = d.type + "|" + d.name + "|" + d.caster + "|" + d.target;
            auto& a = agg[key];
            if (a.count == 0) { a.type = d.type; a.name = d.name; a.caster = d.caster; a.target = d.target; }
            a.total += d.amount;
            a.count += 1;
            if (d.amount > a.maxAmount) a.maxAmount = d.amount;
            if (d.wall > a.lastWall) a.lastWall = d.wall;
        }
        for (auto& kv : agg) detailAggRows.push_back(kv.second);
        std::sort(detailAggRows.begin(), detailAggRows.end(), [](const HealDetailAggRow& a, const HealDetailAggRow& b) {
            if (a.total != b.total) return a.total > b.total;
            return a.name < b.name;
        });
    }

    ImGui::BeginChild("##healing_detail_panel", ImVec2(0, bottomH), true);
    ImGui::TextColored(ImVec4(0.32f, 0.90f, 0.45f, 1.0f), "RUNE / PROC TOTALS BY RECEIVER");
    if (ImGui::BeginTable("##healing_detail_table_future", 5, ImGuiTableFlags_RowBg | ImGuiTableFlags_BordersInnerH | ImGuiTableFlags_SizingStretchProp | ImGuiTableFlags_ScrollY, ImVec2(0, ImGui::GetContentRegionAvail().y))) {
        ImGui::TableSetupColumn("Type", ImGuiTableColumnFlags_WidthFixed, 52);
        ImGui::TableSetupColumn("Receiver", ImGuiTableColumnFlags_WidthStretch, 2.4f);
        ImGui::TableSetupColumn("Total", ImGuiTableColumnFlags_WidthFixed, 58);
        ImGui::TableSetupColumn("Cnt", ImGuiTableColumnFlags_WidthFixed, 36);
        ImGui::TableSetupColumn("Max", ImGuiTableColumnFlags_WidthFixed, 54);
        ImGui::TableHeadersRow();
        int detailShown = 0;
        for (const auto& r : detailAggRows) {
            if (detailShown >= 80) break;
            ImGui::TableNextRow();
            ImGui::TableSetColumnIndex(0); ImGui::TextColored(ImVec4(0.35f, 1.0f, 0.35f, 1.0f), "%s", r.type.c_str());
            ImGui::TableSetColumnIndex(1);
            ImGui::TextColored(ImVec4(0.25f, 0.85f, 1.0f, 1.0f), "%s", r.target.empty() ? r.name.c_str() : r.target.c_str());
            if (ImGui::IsItemHovered()) {
                ImGui::BeginTooltip();
                ImGui::Text("Name: %s", r.name.c_str());
                ImGui::Text("Caster: %s", r.caster.c_str());
                ImGui::Text("Received By: %s", r.target.c_str());
                ImGui::Text("Last: %s", HP_FormatTimeOnly(r.lastWall).c_str());
                ImGui::EndTooltip();
            }
            ImGui::TableSetColumnIndex(2); ImGui::Text("%s", HT_FormatShort(r.total).c_str());
            ImGui::TableSetColumnIndex(3); ImGui::Text("%u", r.count);
            ImGui::TableSetColumnIndex(4); ImGui::Text("%s", HT_FormatShort(r.maxAmount).c_str());
            ++detailShown;
        }
        if (detailShown == 0) { ImGui::TableNextRow(); ImGui::TableSetColumnIndex(1); ImGui::TextDisabled("No rune or proc heals yet."); }
        ImGui::EndTable();
    }
    ImGui::EndChild();

    ImGui::EndChild();
}

static void HP_DrawSpellsPage(float leftW, float rightW)
{
    struct R{std::string n; uint32_t c;}; std::vector<R> rows;
    { std::lock_guard<std::mutex> lk(g_statsMutex); for(auto&kv:g_spellCastsByCaster) rows.push_back({kv.first,kv.second}); }
    std::sort(rows.begin(), rows.end(), [](const R&a,const R&b){return a.c>b.c;});
    ImGui::BeginChild("##spells", ImVec2(0,0), true);
    ImGui::TextColored(ImVec4(.60f,.45f,1,1), "SPELL CASTS");
    if (ImGui::BeginTable("##spells_table", 3, ImGuiTableFlags_RowBg|ImGuiTableFlags_BordersInnerH|ImGuiTableFlags_SizingStretchProp)) {
        ImGui::TableSetupColumn("#", ImGuiTableColumnFlags_WidthFixed, 30); ImGui::TableSetupColumn("Caster"); ImGui::TableSetupColumn("Casts", ImGuiTableColumnFlags_WidthFixed, 80); ImGui::TableHeadersRow(); int i=0; for(auto&r:rows){ ImGui::TableNextRow(); ImGui::TableSetColumnIndex(0); ImGui::Text("%d",++i); ImGui::TableSetColumnIndex(1); ImGui::Text("%s",r.n.c_str()); ImGui::TableSetColumnIndex(2); ImGui::Text("%u",r.c); } ImGui::EndTable();
    }
    ImGui::EndChild();
}

static void HP_DrawTankPage(float leftW, float rightW)
{
    HP_MaybeClearTimedOutLiveTank();
    struct R { std::string n; LiveTankRow t; };
    std::vector<R> rows;
    std::vector<CompletedTankFight> fights;
    uint64_t total = 0;
    uint64_t totalSwings = 0;
    uint32_t totalAvoided = 0;
    int64_t now = NowMs();
    int selectedFight = g_fullUiTankSelectedFight.load();
    bool usingCompleted = false;
    std::string fightMob = "Current Tanking";
    int64_t fightStart = 0;
    int64_t fightEnd = now;

    {
        std::lock_guard<std::mutex> hk(g_completedTankMutex);
        fights = g_completedTankFights;
        if (selectedFight >= (int)fights.size()) {
            selectedFight = fights.empty() ? -1 : 0;
            g_fullUiTankSelectedFight.store(selectedFight);
        }
    }

    if (selectedFight >= 0 && selectedFight < (int)fights.size()) {
        const auto& f = fights[(size_t)selectedFight];
        usingCompleted = true;
        fightMob = f.mob;
        fightStart = f.startedMs;
        fightEnd = f.endedMs ? f.endedMs : now;
        for (const auto& kv : f.tanks) {
            rows.push_back({ kv.first, kv.second });
            total += kv.second.damage;
            totalSwings += HP_TankSwings(kv.second);
            totalAvoided += HP_TankAvoided(kv.second);
        }
    } else {
        selectedFight = -1;
        g_fullUiTankSelectedFight.store(-1);
        {
            std::lock_guard<std::mutex> lk(g_liveTankMutex);
            for (const auto& kv : g_liveTank) {
                rows.push_back({ kv.first, kv.second });
                total += kv.second.damage;
                totalSwings += HP_TankSwings(kv.second);
                totalAvoided += HP_TankAvoided(kv.second);
            }
        }
        // Use the currently selected DPS mob if available so the Tank tab has a mob label while live.
        {
            std::lock_guard<std::mutex> dlk(g_liveDpsMutex);
            if (!g_liveDps.mob.empty()) {
                fightMob = g_liveDps.mob;
                fightStart = g_liveDps.startedMs;
            }
        }
    }

    std::sort(rows.begin(), rows.end(), [](const R& a, const R& b) {
        return a.t.damage > b.t.damage;
    });

    int selectedTank = 0;
    if (!g_fullUiTankSelectedPlayer.empty()) {
        for (int i = 0; i < (int)rows.size(); ++i) {
            if (_stricmp(rows[(size_t)i].n.c_str(), g_fullUiTankSelectedPlayer.c_str()) == 0) {
                selectedTank = i;
                break;
            }
        }
    }

    if (fightStart == 0) {
        for (const auto& r : rows) {
            if (r.t.firstMs && (fightStart == 0 || r.t.firstMs < fightStart)) fightStart = r.t.firstMs;
        }
    }
    int dur = fightStart ? (int)std::max<int64_t>(1, (fightEnd - fightStart) / 1000) : 0;
    double raidAvoid = totalSwings ? (100.0 * (double)totalAvoided / (double)totalSwings) : 0.0;

    const float fightListW = 235.0f;
    const float detailW = std::max(420.0f, leftW - fightListW - 8.0f);

    ImGui::BeginChild("##tank_fight_selector", ImVec2(fightListW, 0), true);
    ImGui::TextColored(ImVec4(1.0f, .72f, .24f, 1.0f), "TANK FIGHTS");
    ImGui::Separator();
    if (ImGui::Selectable("LIVE: Current tanking", selectedFight < 0, ImGuiSelectableFlags_SpanAllColumns)) {
        g_fullUiTankSelectedFight.store(-1);
    }
    ImGui::Spacing();
    ImGui::TextDisabled("COMPLETED");
    if (fights.empty()) {
        ImGui::TextDisabled("No completed tank fights yet.");
    } else {
        for (int i = 0; i < (int)fights.size(); ++i) {
            const auto& f = fights[(size_t)i];
            int fdur = (int)std::max<int64_t>(1, (f.endedMs - f.startedMs) / 1000);
            char label[256];
            std::snprintf(label, sizeof(label), "%s##tankfight%d", f.mob.c_str(), i);
            bool sel = selectedFight == i;
            if (ImGui::Selectable(label, sel, ImGuiSelectableFlags_SpanAllColumns)) {
                g_fullUiTankSelectedFight.store(i);
                selectedFight = i;
            }
            ImGui::TextDisabled("  %s  %ds", HT_FormatShort(f.total).c_str(), fdur);
        }
    }
    ImGui::EndChild();

    ImGui::SameLine();
    ImGui::BeginChild("##tank_main", ImVec2(detailW, 0), true);
    ImGui::TextColored(ImVec4(1.0f, .32f, .32f, 1.0f), "%s", fightMob.c_str());
    if (usingCompleted) ImGui::SameLine(), ImGui::TextDisabled("completed");
    else ImGui::SameLine(), ImGui::TextDisabled("live");

    HP_StatCard("TANK DAMAGE", HT_FormatShort(total), IM_COL32(255, 190, 60, 255)); ImGui::SameLine();
    HP_StatCard("RAID DTPS", HT_FormatInteger(dur ? total / (uint64_t)dur : 0), IM_COL32(255, 190, 60, 255)); ImGui::SameLine();
    HP_StatCard("SWINGS", HT_FormatInteger(totalSwings), IM_COL32(255, 190, 60, 255)); ImGui::SameLine();
    char avoidBuf[32]; std::snprintf(avoidBuf, sizeof(avoidBuf), "%.1f%%", raidAvoid);
    HP_StatCard("AVOID", avoidBuf, IM_COL32(255, 190, 60, 255));
    ImGui::Separator();
    ImGui::TextColored(ImVec4(1.0f, .72f, .24f, 1.0f), "TANK DAMAGE TAKEN");
    ImGui::TextDisabled("Click a tank row to show worst spike, last 10 hits, and avoidance details on the right.");

    if (ImGui::BeginTable("##tank_table_detail", 14, ImGuiTableFlags_RowBg | ImGuiTableFlags_BordersInnerH | ImGuiTableFlags_SizingStretchProp | ImGuiTableFlags_Resizable)) {
        ImGui::TableSetupColumn("#", ImGuiTableColumnFlags_WidthFixed, 28);
        ImGui::TableSetupColumn("Tank");
        ImGui::TableSetupColumn("Damage", ImGuiTableColumnFlags_WidthFixed, 82);
        ImGui::TableSetupColumn("DTPS", ImGuiTableColumnFlags_WidthFixed, 62);
        ImGui::TableSetupColumn("Hits", ImGuiTableColumnFlags_WidthFixed, 50);
        ImGui::TableSetupColumn("Swings", ImGuiTableColumnFlags_WidthFixed, 58);
        ImGui::TableSetupColumn("Avoid", ImGuiTableColumnFlags_WidthFixed, 56);
        ImGui::TableSetupColumn("Avg", ImGuiTableColumnFlags_WidthFixed, 62);
        ImGui::TableSetupColumn("Max", ImGuiTableColumnFlags_WidthFixed, 62);
        ImGui::TableSetupColumn("Miss", ImGuiTableColumnFlags_WidthFixed, 48);
        ImGui::TableSetupColumn("Dodge", ImGuiTableColumnFlags_WidthFixed, 52);
        ImGui::TableSetupColumn("Parry", ImGuiTableColumnFlags_WidthFixed, 52);
        ImGui::TableSetupColumn("Rip", ImGuiTableColumnFlags_WidthFixed, 42);
        ImGui::TableSetupColumn("Block", ImGuiTableColumnFlags_WidthFixed, 50);
        ImGui::TableHeadersRow();

        int idx = 0;
        for (auto& r : rows) {
            uint64_t swings = HP_TankSwings(r.t);
            uint32_t avoided = HP_TankAvoided(r.t);
            double avoidPct = swings ? (100.0 * (double)avoided / (double)swings) : 0.0;
            uint64_t avg = r.t.hits ? r.t.damage / r.t.hits : 0;
            int rowDur = r.t.firstMs ? (int)std::max<int64_t>(1, ((usingCompleted ? fightEnd : now) - r.t.firstMs) / 1000) : dur;
            uint64_t dtps = rowDur ? r.t.damage / (uint64_t)rowDur : 0;

            ImGui::TableNextRow(ImGuiTableRowFlags_None, 24.0f);
            ImGui::TableSetColumnIndex(0); ImGui::Text("%d", ++idx);
            ImGui::TableSetColumnIndex(1);
            bool sel = (idx - 1) == selectedTank;
            if (ImGui::Selectable(r.n.c_str(), sel, ImGuiSelectableFlags_SpanAllColumns | ImGuiSelectableFlags_AllowItemOverlap)) {
                g_fullUiTankSelectedPlayer = r.n;
                selectedTank = idx - 1;
            }
            ImGui::TableSetColumnIndex(2); ImGui::Text("%s", HT_FormatShort(r.t.damage).c_str());
            ImGui::TableSetColumnIndex(3); ImGui::Text("%s", HT_FormatInteger(dtps).c_str());
            ImGui::TableSetColumnIndex(4); ImGui::Text("%u", r.t.hits);
            ImGui::TableSetColumnIndex(5); ImGui::Text("%llu", (unsigned long long)swings);
            ImGui::TableSetColumnIndex(6); ImGui::Text("%.1f%%", avoidPct);
            ImGui::TableSetColumnIndex(7); ImGui::Text("%s", HT_FormatInteger(avg).c_str());
            ImGui::TableSetColumnIndex(8); ImGui::Text("%u", r.t.maxHit);
            ImGui::TableSetColumnIndex(9); ImGui::Text("%u", r.t.misses);
            ImGui::TableSetColumnIndex(10); ImGui::Text("%u", r.t.dodges);
            ImGui::TableSetColumnIndex(11); ImGui::Text("%u", r.t.parries);
            ImGui::TableSetColumnIndex(12); ImGui::Text("%u", r.t.ripostes);
            ImGui::TableSetColumnIndex(13); ImGui::Text("%u", r.t.blocks);
        }
        ImGui::EndTable();
    }
    ImGui::EndChild();

    ImGui::SameLine();
    ImGui::BeginChild("##tank_side", ImVec2(rightW, 0), true);
    ImGui::TextColored(ImVec4(1.0f, .72f, .24f, 1.0f), "TANK DETAIL");
    ImGui::Separator();
    if (rows.empty()) {
        ImGui::TextDisabled("No tanking data yet.");
    } else {
        if (selectedTank >= (int)rows.size()) selectedTank = 0;
        const auto& r = rows[(size_t)selectedTank];
        const LiveTankRow& t = r.t;
        uint64_t swings = HP_TankSwings(t);
        uint32_t avoided = HP_TankAvoided(t);
        double avoidPct = swings ? (100.0 * (double)avoided / (double)swings) : 0.0;
        uint64_t avg = t.hits ? t.damage / t.hits : 0;
        uint64_t worst = HP_TankWorstSpike3s(t);
        int rowDur = t.firstMs ? (int)std::max<int64_t>(1, ((usingCompleted ? fightEnd : now) - t.firstMs) / 1000) : dur;
        uint64_t dtps = rowDur ? t.damage / (uint64_t)rowDur : 0;

        ImGui::TextColored(ImVec4(.35f, .72f, 1.0f, 1.0f), "%s", r.n.c_str());
        ImGui::TextDisabled("Damage %s | DTPS %s", HT_FormatShort(t.damage).c_str(), HT_FormatInteger(dtps).c_str());
        ImGui::Spacing();
        ImGui::Text("Hits: %u", t.hits);
        ImGui::Text("Swings: %llu", (unsigned long long)swings);
        ImGui::Text("Avoided: %u (%.1f%%)", avoided, avoidPct);
        ImGui::Text("Average Hit: %s", HT_FormatInteger(avg).c_str());
        ImGui::Text("Max Hit: %u", t.maxHit);
        ImGui::Text("Worst 3s Spike: %s", HT_FormatShort(worst).c_str());
        ImGui::Separator();
        ImGui::TextColored(ImVec4(1.0f, .72f, .24f, 1.0f), "AVOIDANCE");
        ImGui::Text("Miss: %u", t.misses);
        ImGui::Text("Dodge: %u", t.dodges);
        ImGui::Text("Parry: %u", t.parries);
        ImGui::Text("Riposte: %u", t.ripostes);
        ImGui::Text("Block: %u", t.blocks);
        ImGui::Separator();
        ImGui::TextColored(ImVec4(1.0f, .32f, .32f, 1.0f), "LAST 10 HITS");
        if (t.lastHits.empty()) {
            ImGui::TextDisabled("No hit recap yet.");
        } else if (ImGui::BeginTable("##last10_tank_hits", 4, ImGuiTableFlags_RowBg | ImGuiTableFlags_BordersInnerH | ImGuiTableFlags_SizingStretchProp)) {
            ImGui::TableSetupColumn("Ago", ImGuiTableColumnFlags_WidthFixed, 42);
            ImGui::TableSetupColumn("Mob");
            ImGui::TableSetupColumn("Amt", ImGuiTableColumnFlags_WidthFixed, 62);
            ImGui::TableSetupColumn("Type", ImGuiTableColumnFlags_WidthFixed, 64);
            ImGui::TableHeadersRow();
            for (auto it = t.lastHits.rbegin(); it != t.lastHits.rend(); ++it) {
                int ago = usingCompleted ? (int)std::max<int64_t>(0, (fightEnd - it->ms) / 1000) : (int)std::max<int64_t>(0, (now - it->ms) / 1000);
                ImGui::TableNextRow();
                ImGui::TableSetColumnIndex(0); ImGui::Text("%ds", ago);
                ImGui::TableSetColumnIndex(1); ImGui::Text("%s", it->attacker.c_str());
                ImGui::TableSetColumnIndex(2); ImGui::Text("%u", it->amount);
                ImGui::TableSetColumnIndex(3); ImGui::Text("%s", it->type.c_str());
            }
            ImGui::EndTable();
        }
    }
    ImGui::EndChild();
}

static void HP_DrawHealsPageWithFightList(float leftW, float rightW)
{
    const float fightsW = std::min(480.0f, std::max(410.0f, leftW * 0.34f));
    const float mainW = std::max(520.0f, leftW - fightsW - 10.0f);
    HP_DrawDpsFightList(fightsW);
    ImGui::SameLine();
    HP_DrawHealsPage(mainW, rightW);
}

static void HP_DrawSpellsPageWithFightList(float leftW, float rightW)
{
    const float fightsW = std::min(480.0f, std::max(410.0f, leftW * 0.34f));
    HP_DrawDpsFightList(fightsW);
    ImGui::SameLine();
    ImGui::BeginChild("##spells_main_with_fights", ImVec2(0, 0), false);
    HP_DrawSpellsPage(leftW - fightsW - 10.0f, rightW);
    ImGui::EndChild();
}


static void HP_DrawCommandsWindow()
{
    if (!g_showCommandsWindow) return;

    ImGui::SetNextWindowSize(ImVec2(760.0f, 620.0f), ImGuiCond_FirstUseEver);
    if (ImGui::Begin("HealParse Commands###HealParseCommandsWindow", &g_showCommandsWindow, ImGuiWindowFlags_NoCollapse)) {
        ImGui::TextColored(ImVec4(.32f,.72f,1,1), "INGAME COMMANDS");
        ImGui::TextDisabled("Type these in-game from the MQ/EQ command line.");
        ImGui::Separator();

        if (ImGui::BeginTable("##healparse_commands_table", 2,
            ImGuiTableFlags_RowBg | ImGuiTableFlags_BordersInnerH | ImGuiTableFlags_BordersOuterH | ImGuiTableFlags_SizingStretchProp | ImGuiTableFlags_ScrollY,
            ImVec2(0, 0))) {
            ImGui::TableSetupColumn("Command", ImGuiTableColumnFlags_WidthStretch, 0.42f);
            ImGui::TableSetupColumn("Description", ImGuiTableColumnFlags_WidthStretch, 0.58f);
            ImGui::TableHeadersRow();

            auto row = [](const char* cmd, const char* desc) {
                ImGui::TableNextRow();
                ImGui::TableSetColumnIndex(0); ImGui::TextWrapped("%s", cmd);
                ImGui::TableSetColumnIndex(1); ImGui::TextWrapped("%s", desc);
            };

            row("/healparse", "Shows parser status and current counters.");
            row("/healparse on", "Turns the parser on.");
            row("/healparse off", "Turns the parser off without unloading the plugin.");
            row("/healparse pause", "Temporarily pauses parsing.");
            row("/healparse resume", "Resumes parsing after pause.");
            row("/healparse reset", "Clears current plugin stats while keeping known characters and pet links.");
            row("/healparse debug on|off", "Turns parse debug messages on or off.");
            row("/healparse audit on|off", "Writes counted, dropped, source, and raw combat rows to <MQ root>\\MQ2HealParse_Audit\\MQ2HealParse_Audit.tsv.");
            row("/healparse audit player <name|all>", "Limits the audit log to one player, such as Forrage, Kreampie, Arbys, or all players.");
            row("/healparse audit clear", "Clears the audit TSV and writes a fresh header row. /healparse audit path prints the exact location.");
            row("/healparse dedup spell on|off", "Turns cross-form spell damage de-dupe on or off. Default is off to match GamParse's final EQ log.");
            row("/healparse push on|off", "Controls whether parsed events are pushed to the Lua bridge.");
            row("/healparse minheal <number>", "Sets the minimum heal amount recorded by the plugin.");
            row("/healparse ui on", "Opens the full HealTracker plugin UI.");
            row("/healparse ui off", "Closes the full HealTracker plugin UI.");
            row("/healparse ui reset", "Resets and centers the full UI so it is not stuck off-screen.");
            row("/healparse ui center", "Centers the full UI on the screen.");
            row("/healparse overlay on|off", "Shows or hides the mini live overlay.");
            row("/healparse overlay resetpos", "Resets the mini overlay position.");
            row("/healparse overlay alpha <15-100>", "Adjusts mini overlay transparency.");
            row("/healparse view dps", "Switches the mini overlay to DPS view.");
            row("/healparse view heals", "Switches the mini overlay to Heals view.");
            row("/healparse view burns", "Switches the mini overlay to Burns/Timers view.");
            row("/healparse pet link <owner> <pet name>", "Manually links a pet to an owner. Swarm pets named <Owner>'s pet now auto-link without this.");
            row("/healparse pet add <pet> <owner>", "Legacy single-word pet link command.");
            row("/healparse pet del <pet name>", "Removes a pet-owner link.");
            row("/healparse pet list", "Lists all linked pets and owners.");
            row("/healparse pet clear", "Clears every saved pet-owner link.");
            row("/healparse pet save", "Saves current pet links to MQ2HealParse_PetOwners.tsv.");
            row("/healparse pet load", "Reloads saved pet links from MQ2HealParse_PetOwners.tsv.");
            row("/healparse charm test <mob name>", "Checks whether a named NPC spawn is currently charmed and who owns it.");
            row("/healparse charm cache", "Shows the short-lived charmed pet owner cache.");
            row("/healparse charm clear", "Clears the charmed pet owner cache.");
            row("/healparse burn <who>|<label>|<seconds>", "Adds or refreshes a live burn/timer entry.");
            row("/healparse burn clear", "Clears all live burn/timer entries.");
            row("/healparse burnrule add <trigger>|<display>|<seconds>", "Saves an MQ/EQ text trigger that starts a burn timer when seen.");
            row("/healparse burnrule list", "Lists saved burn timer triggers.");
            row("/healparse burnrule clear", "Deletes all saved burn timer triggers.");
            row("/healparse imgtest", "Tests image/icon loading paths.");
            row("/plugin mq2healparse", "Loads the plugin if it is not already loaded.");
            row("/plugin mq2healparse unload", "Unloads the plugin.");
            ImGui::EndTable();
        }
    }
    ImGui::End();
}


static void HP_DrawPetOwnersWindow()
{
    if (!g_showPetOwnersWindow) return;

    static char petNameBuf[128] = "";
    static char ownerNameBuf[64] = "";
    static char filterBuf[96] = "";

    ImGui::SetNextWindowSize(ImVec2(760.0f, 640.0f), ImGuiCond_FirstUseEver);
    if (ImGui::Begin("Linked Pet Owners###HealParsePetOwnersWindow", &g_showPetOwnersWindow, ImGuiWindowFlags_NoCollapse)) {
        ImGui::TextColored(ImVec4(.32f,.72f,1,1), "LINKED PET OWNERS");
        ImGui::SameLine();
        ImGui::TextDisabled(g_dpsCombinePets ? "Player Damage: pets combined" : "Player Damage: pets split");
        ImGui::Separator();

        std::vector<std::string> petCandidates;
        std::vector<std::string> ownerCandidates;
        HP_GetPetOwnerPickerLists(petCandidates, ownerCandidates);

        ImGui::TextColored(ImVec4(.45f,1.0f,.45f,1), "Manual Link / Update");
        ImGui::Text("Pet Name");
        ImGui::SetNextItemWidth(-1.0f);
        ImGui::InputText("##PetNameManualInput", petNameBuf, IM_ARRAYSIZE(petNameBuf));
        if (!petCandidates.empty()) {
            ImGui::Text("Pick from seen / linked pet names");
            ImGui::SetNextItemWidth(-1.0f);
            if (ImGui::BeginCombo("##PickPetFromSeenLinked", petNameBuf[0] ? petNameBuf : "Select a pet name")) {
                for (const std::string& pet : petCandidates) {
                    bool selected = (_stricmp(petNameBuf, pet.c_str()) == 0);
                    if (ImGui::Selectable(pet.c_str(), selected))
                        HP_CopyStringToBuffer(petNameBuf, IM_ARRAYSIZE(petNameBuf), pet);
                    if (selected) ImGui::SetItemDefaultFocus();
                }
                ImGui::EndCombo();
            }
        } else {
            ImGui::TextDisabled("No pet candidates found yet. Type the pet name manually, or fight once with pets visible.");
        }

        ImGui::Text("Owner");
        ImGui::SetNextItemWidth(-1.0f);
        ImGui::InputText("##OwnerNameManualInput", ownerNameBuf, IM_ARRAYSIZE(ownerNameBuf));
        if (!ownerCandidates.empty()) {
            ImGui::Text("Pick from seen players");
            ImGui::SetNextItemWidth(-1.0f);
            if (ImGui::BeginCombo("##PickOwnerFromSeenPlayers", ownerNameBuf[0] ? ownerNameBuf : "Select an owner")) {
                for (const std::string& owner : ownerCandidates) {
                    bool selected = (_stricmp(ownerNameBuf, owner.c_str()) == 0);
                    if (ImGui::Selectable(owner.c_str(), selected))
                        HP_CopyStringToBuffer(ownerNameBuf, IM_ARRAYSIZE(ownerNameBuf), owner);
                    if (selected) ImGui::SetItemDefaultFocus();
                }
                ImGui::EndCombo();
            }
        }

        if (ImGui::Button("Link / Update Pet Owner", ImVec2(210.0f, 0.0f))) {
            std::string pet = HP_TrimCopy(petNameBuf);
            std::string owner = HP_TrimCopy(ownerNameBuf);
            if (!pet.empty() && !owner.empty()) {
                HP_SetPetOwner(pet, owner, true);
                petNameBuf[0] = '\0';
                ownerNameBuf[0] = '\0';
            } else {
                WriteChatf("\ar[HealParse]\ax Pet Name and Owner Name are required.");
            }
        }
        ImGui::SameLine();
        if (ImGui::Button("Clear Entry", ImVec2(110.0f, 0.0f))) {
            petNameBuf[0] = '\0';
            ownerNameBuf[0] = '\0';
        }
        ImGui::SameLine();
        if (ImGui::Button("Save Links", ImVec2(110.0f, 0.0f))) {
            std::lock_guard<std::mutex> lk(g_statsMutex);
            HP_SavePetOwnersUnlocked();
            WriteChatf("\ag[HealParse]\ax pet links saved.");
        }


        ImGui::Spacing();
        ImGui::Separator();
        ImGui::TextColored(ImVec4(.32f,.72f,1,1), "CURRENT LINKS");
        ImGui::SameLine();
        ImGui::SetNextItemWidth(220.0f);
        ImGui::InputText("Filter", filterBuf, IM_ARRAYSIZE(filterBuf));

        auto petLinks = HP_GetPetOwnerLinksForUi();
        std::string filter = LowerCopy(HP_TrimCopy(filterBuf));

        if (petLinks.empty()) {
            ImGui::TextDisabled("No pets linked yet. Swarm pets named <Owner>'s pet auto-link when first seen.");
        } else if (ImGui::BeginTable("##pet_owner_links_popup_table", 4,
            ImGuiTableFlags_RowBg | ImGuiTableFlags_BordersInnerH | ImGuiTableFlags_BordersOuterH | ImGuiTableFlags_SizingStretchProp | ImGuiTableFlags_ScrollY,
            ImVec2(0, 0))) {
            ImGui::TableSetupColumn("Owner", ImGuiTableColumnFlags_WidthStretch, 0.30f);
            ImGui::TableSetupColumn("Pet", ImGuiTableColumnFlags_WidthStretch, 0.48f);
            ImGui::TableSetupColumn("Edit", ImGuiTableColumnFlags_WidthFixed, 70.0f);
            ImGui::TableSetupColumn("Remove", ImGuiTableColumnFlags_WidthFixed, 82.0f);
            ImGui::TableHeadersRow();

            int idx = 0;
            for (const auto& link : petLinks) {
                std::string hay = LowerCopy(link.second + " " + link.first);
                if (!filter.empty() && hay.find(filter) == std::string::npos) continue;

                ImGui::TableNextRow();
                ImGui::TableSetColumnIndex(0); ImGui::TextColored(ImVec4(.45f,1.0f,.45f,1), "%s", link.second.c_str());
                ImGui::TableSetColumnIndex(1); ImGui::TextWrapped("%s", link.first.c_str());
                ImGui::TableSetColumnIndex(2);
                ImGui::PushID(idx);
                if (ImGui::SmallButton("Use")) {
                    HP_CopyStringToBuffer(petNameBuf, IM_ARRAYSIZE(petNameBuf), link.first);
                    HP_CopyStringToBuffer(ownerNameBuf, IM_ARRAYSIZE(ownerNameBuf), link.second);
                }
                ImGui::TableSetColumnIndex(3);
                if (ImGui::SmallButton("Delete")) {
                    std::lock_guard<std::mutex> lk(g_statsMutex);
                    g_petOwners.erase(link.first);
                    HP_SavePetOwnersUnlocked();
                }
                ImGui::PopID();
                ++idx;
            }
            ImGui::EndTable();
        }
    }
    ImGui::End();
}

static void HP_DrawBurnTimersWindow()
{
    if (!g_showBurnTimersWindow) return;

    static char triggerBuf[160] = "";
    static char displayBuf[96] = "";
    static int secondsBuf = 120;
    static bool enabledBuf = true;
    static char pickerSearchBuf[128] = "";
    static bool pickerListOpen = false;
    static char filterBuf[96] = "";
    static bool editMode = false;
    static char editOriginalTrigger[160] = "";

    ImGui::SetNextWindowSize(ImVec2(900.0f, 700.0f), ImGuiCond_FirstUseEver);
    if (ImGui::Begin("Burn Timer Triggers###HealParseBurnTimersWindow", &g_showBurnTimersWindow, ImGuiWindowFlags_NoCollapse)) {
        ImGui::TextColored(ImVec4(.32f,.72f,1,1), "BURN TIMER TRIGGERS");
        ImGui::SameLine();
        ImGui::TextDisabled("Detected MQ2 window text starts timers on the mini Burn view.");
        ImGui::Separator();

        std::vector<std::string> spellNames;
        HP_GetKnownSpellNamesForBurnPicker(spellNames);

        ImGui::TextColored(ImVec4(.45f,1.0f,.45f,1), "Add / Update Burn Timer");

        ImGui::Text("Manually type item / spell name to watch for");
        ImGui::SetNextItemWidth(-1.0f);
        ImGui::InputText("##BurnTriggerManualItemSpellName", triggerBuf, IM_ARRAYSIZE(triggerBuf));
        ImGui::TextDisabled("Example: Staff of Ancient Power, Improved Twincast, Epic: Staff of Ancient Power");

        if (!spellNames.empty()) {
            ImGui::Spacing();
            ImGui::Text("Or search previous spells / burns");

            const float openButtonWidth = 95.0f;
            ImGui::SetNextItemWidth(std::max(120.0f, ImGui::GetContentRegionAvail().x - openButtonWidth - ImGui::GetStyle().ItemSpacing.x));
            bool pickerTyped = ImGui::InputText("##BurnTriggerPreviousSpellSearch", pickerSearchBuf, IM_ARRAYSIZE(pickerSearchBuf));
            if (pickerTyped || ImGui::IsItemActivated()) {
                pickerListOpen = true;
            }
            if (ImGui::IsItemHovered()) {
                ImGui::SetTooltip("Type here to filter previous spells/burns. The list stays under this search box so you can keep typing.");
            }

            ImGui::SameLine();
            if (ImGui::SmallButton(pickerListOpen ? "Hide List" : "Show List")) {
                pickerListOpen = !pickerListOpen;
            }

            if (pickerListOpen) {
                std::string pickFilter = LowerCopy(pickerSearchBuf);
                int shown = 0;

                ImGui::BeginChild("##BurnTriggerPreviousSpellListBox", ImVec2(0.0f, 180.0f), true);
                for (const std::string& n : spellNames) {
                    if (!pickFilter.empty() && LowerCopy(n).find(pickFilter) == std::string::npos)
                        continue;

                    bool selected = (_stricmp(triggerBuf, n.c_str()) == 0);
                    if (ImGui::Selectable(n.c_str(), selected)) {
                        HP_CopyStringToBuffer(triggerBuf, IM_ARRAYSIZE(triggerBuf), n);
                        HP_CopyStringToBuffer(pickerSearchBuf, IM_ARRAYSIZE(pickerSearchBuf), n);
                        pickerListOpen = false;
                    }
                    if (++shown >= 150) {
                        ImGui::TextDisabled("Showing first 150 matches. Type more to narrow the list.");
                        break;
                    }
                }
                if (shown == 0) {
                    ImGui::TextDisabled("No previous spells/burns match that search.");
                }
                ImGui::EndChild();
            }
        }

        ImGui::Text("Display name shown on mini live burn timer");
        ImGui::SetNextItemWidth(-1.0f);
        ImGui::InputText("##BurnTriggerDisplayName", displayBuf, IM_ARRAYSIZE(displayBuf));

        ImGui::Text("Recast time / timer amount in seconds");
        ImGui::SetNextItemWidth(180.0f);
        ImGui::InputInt("##BurnTriggerRecastSeconds", &secondsBuf, 5, 30);
        if (secondsBuf < 1) secondsBuf = 1;
        if (secondsBuf > 36000) secondsBuf = 36000;

        ImGui::Checkbox("Enabled", &enabledBuf);

        const char* saveLabel = editMode ? "Update Burn Timer" : "Save Burn Timer";
        if (ImGui::Button(saveLabel, ImVec2(190.0f, 0.0f))) {
            std::string trigger = HP_TrimCopy(triggerBuf);
            if (!trigger.empty()) {
                std::string original = HP_TrimCopy(editOriginalTrigger);

                // If editing and the item/spell name was changed, remove the old rule first
                // so updating does not leave a duplicate behind.
                if (editMode && !original.empty() && LowerCopy(original) != LowerCopy(trigger)) {
                    std::lock_guard<std::mutex> lk(g_burnTriggerRulesMutex);
                    for (auto it = g_burnTriggerRules.begin(); it != g_burnTriggerRules.end(); ++it) {
                        if (LowerCopy(it->trigger) == LowerCopy(original)) {
                            g_burnTriggerRules.erase(it);
                            break;
                        }
                    }
                    HP_SaveBurnTriggersUnlocked();
                }

                HP_SetBurnTriggerRule(trigger, displayBuf, secondsBuf, enabledBuf);

                // Clear the add/update fields after saving so the user can enter the next burn cleanly.
                triggerBuf[0] = '\0';
                displayBuf[0] = '\0';
                pickerSearchBuf[0] = '\0';
                editOriginalTrigger[0] = '\0';
                secondsBuf = 120;
                enabledBuf = true;
                pickerListOpen = false;
                editMode = false;
            }
        }
        ImGui::SameLine();
        if (ImGui::Button("Test Timer", ImVec2(120.0f, 0.0f))) {
            std::string trigger = HP_TrimCopy(triggerBuf);
            std::string label = HP_TrimCopy(displayBuf);
            if (label.empty()) label = trigger;
            if (!label.empty()) {
                std::string testWho = "Test";
                if (auto pChar = GetCharInfo()) {
                    if (pChar->Name[0]) testWho = pChar->Name;
                }
                AddLiveBurn(testWho, label, secondsBuf);
                g_liveOverlayView.store(2);
                g_liveOverlayEnabled.store(true);
            }
        }
        ImGui::SameLine();
        if (ImGui::Button("Clear Fields", ImVec2(120.0f, 0.0f))) {
            triggerBuf[0] = '\0';
            displayBuf[0] = '\0';
            pickerSearchBuf[0] = '\0';
            editOriginalTrigger[0] = '\0';
            secondsBuf = 120;
            enabledBuf = true;
            editMode = false;
        }

        ImGui::Spacing();
        ImGui::Separator();

        ImGui::Text("Filter saved burn timers");
        ImGui::SetNextItemWidth(-1.0f);
        ImGui::InputText("##BurnTriggerSavedFilter", filterBuf, IM_ARRAYSIZE(filterBuf));

        auto rules = HP_GetBurnTriggerRulesForUi();
        ImGui::TextDisabled("%zu saved burn timer(s). Leave display name blank to show the original item/spell name.", rules.size());

        if (ImGui::BeginTable("##BurnTimerRulesTable", 6, ImGuiTableFlags_RowBg | ImGuiTableFlags_BordersH | ImGuiTableFlags_SizingStretchProp | ImGuiTableFlags_ScrollY, ImVec2(0, 300.0f))) {
            ImGui::TableSetupColumn("Enabled", ImGuiTableColumnFlags_WidthFixed, 70.0f);
            ImGui::TableSetupColumn("Item / Spell Name", ImGuiTableColumnFlags_WidthStretch, 1.45f);
            ImGui::TableSetupColumn("Display Name", ImGuiTableColumnFlags_WidthStretch, 1.0f);
            ImGui::TableSetupColumn("Recast Time", ImGuiTableColumnFlags_WidthFixed, 95.0f);
            ImGui::TableSetupColumn("Edit", ImGuiTableColumnFlags_WidthFixed, 70.0f);
            ImGui::TableSetupColumn("Delete", ImGuiTableColumnFlags_WidthFixed, 80.0f);
            ImGui::TableHeadersRow();

            std::string filter = LowerCopy(filterBuf);
            int idx = 0;
            for (const auto& r : rules) {
                std::string hay = LowerCopy(r.trigger + " " + r.display);
                if (!filter.empty() && hay.find(filter) == std::string::npos) { ++idx; continue; }

                ImGui::TableNextRow();
                ImGui::TableSetColumnIndex(0);
                ImGui::PushID(idx);
                bool on = r.enabled;
                if (ImGui::Checkbox("##enabled", &on)) {
                    HP_SetBurnTriggerRule(r.trigger, r.display, r.seconds, on);
                }
                ImGui::TableSetColumnIndex(1); ImGui::TextWrapped("%s", r.trigger.c_str());
                ImGui::TableSetColumnIndex(2); ImGui::TextWrapped("%s", r.display.empty() ? r.trigger.c_str() : r.display.c_str());
                ImGui::TableSetColumnIndex(3); ImGui::Text("%d sec", r.seconds);
                ImGui::TableSetColumnIndex(4);
                if (ImGui::SmallButton("Edit")) {
                    HP_CopyStringToBuffer(triggerBuf, IM_ARRAYSIZE(triggerBuf), r.trigger);
                    HP_CopyStringToBuffer(displayBuf, IM_ARRAYSIZE(displayBuf), r.display);
                    HP_CopyStringToBuffer(editOriginalTrigger, IM_ARRAYSIZE(editOriginalTrigger), r.trigger);
                    pickerSearchBuf[0] = '\0';
                    secondsBuf = r.seconds;
                    enabledBuf = r.enabled;
                    pickerListOpen = false;
                    editMode = true;
                }
                ImGui::TableSetColumnIndex(5);
                if (ImGui::SmallButton("Delete")) {
                    std::lock_guard<std::mutex> lk(g_burnTriggerRulesMutex);
                    for (auto it = g_burnTriggerRules.begin(); it != g_burnTriggerRules.end(); ++it) {
                        if (LowerCopy(it->trigger) == LowerCopy(r.trigger)) {
                            g_burnTriggerRules.erase(it);
                            break;
                        }
                    }
                    HP_SaveBurnTriggersUnlocked();
                }
                ImGui::PopID();
                ++idx;
            }
            ImGui::EndTable();
        }

        ImGui::Spacing();
        ImGui::TextWrapped("Example: Item / Spell Name = Improved Twincast, Display Name = ITC, Recast Time = 120. When a line in the MQ2 window contains Improved Twincast, the mini overlay switches to Burn Timers and counts down ITC for that character.");
    }
    ImGui::End();
}

static void HP_DrawSettingsPage()
{
    ImGui::BeginChild("##settings", ImVec2(0,0), true);
    ImGui::TextColored(ImVec4(.32f,.72f,1,1), "PLUGIN UI SETTINGS");
    ImGui::Separator();
    int alpha = g_liveOverlayAlphaPercent.load();
    if (ImGui::SliderInt("Overlay Alpha", &alpha, 15, 100)) g_liveOverlayAlphaPercent.store(alpha);
    int linger = g_afterFightPopupLingerSec.load();
    if (ImGui::SliderInt("After-fight popup seconds", &linger, 3, 60)) g_afterFightPopupLingerSec.store(linger);
    bool popupEnabled = g_enableAfterFightPopup.load();
    if (ImGui::Checkbox("Show Last Fight Popup", &popupEnabled)) {
        g_enableAfterFightPopup.store(popupEnabled);
        if (!popupEnabled) g_afterFightPopupOpen.store(false);
    }
    bool mini = g_liveOverlayEnabled.load();
    if (ImGui::Checkbox("Show mini plugin overlay", &mini)) g_liveOverlayEnabled.store(mini);
    bool full = g_fullUiEnabled.load();
    if (ImGui::Checkbox("Show full plugin UI", &full)) g_fullUiEnabled.store(full);
    if (ImGui::Button("Reset Mini Position")) { g_liveOverlayResetPos.store(true); g_liveOverlayForceVisible.store(true); }
    ImGui::SameLine();
    if (ImGui::Button("Center Full UI")) {
        g_fullUiResetPos.store(true);
        g_fullUiEnabled.store(true);
    }
    ImGui::SameLine();
    if (ImGui::Button("Commands")) {
        g_showCommandsWindow = true;
    }
    ImGui::SameLine();
    if (ImGui::Button("Burn Timers")) {
        g_showBurnTimersWindow = true;
    }
    ImGui::SameLine();
    ImGui::TextDisabled("Add MQ/EQ text triggers that start countdowns on the mini Burn view.");
    ImGui::Spacing();
    ImGui::Separator();
    auto petLinks = HP_GetPetOwnerLinksForUi();
    ImGui::TextColored(ImVec4(.32f,.72f,1,1), "LINKED PET OWNERS");
    ImGui::SameLine();
    ImGui::TextDisabled("%zu linked  |  %s", petLinks.size(), g_dpsCombinePets ? "pets combined" : "pets split");
    if (ImGui::Button("Linked Pet Owners", ImVec2(220.0f, 0.0f))) {
        g_showPetOwnersWindow = true;
    }
    ImGui::SameLine();
    ImGui::TextDisabled("Open this to view, edit, delete, or manually link pets.");
    ImGui::Spacing();
    ImGui::TextWrapped("Click Commands above for the full ingame command list. Swarm pets named <Owner>'s pet are auto-linked and saved the first time they are seen. Use Audit while testing against GamParse to see exactly what was counted or dropped per player.");
    ImGui::EndChild();
}

void DrawHealParseFullUi()
{
    g_fullUiFrames.fetch_add(1, std::memory_order_relaxed);
    if (!g_fullUiEnabled.load()) return;

    HP_SetFullUiTheme();
    ImVec2 hpFullSafeSize = HP_GetSafeFullUiSize();
    ImGui::SetNextWindowSize(hpFullSafeSize, ImGuiCond_FirstUseEver);
    ImGui::SetNextWindowSizeConstraints(ImVec2(1180, 700), ImVec2(FLT_MAX, FLT_MAX));

    // Reset always moves the main UI to the visible center of the screen.
    // This prevents the full UI from getting stuck at the very top/off-screen.
    if (g_fullUiResetPos.exchange(false)) {
        ImGui::SetNextWindowPos(HP_GetCenteredFullUiPos(), ImGuiCond_Always);
        ImGui::SetNextWindowSize(hpFullSafeSize, ImGuiCond_Always);
    }

    bool open = true;
    ImGuiWindowFlags flags = ImGuiWindowFlags_NoCollapse;
    if (ImGui::Begin("HealTracker Plugin UI###HealParseFullPluginUI", &open, flags)) {
        ImDrawList* dl = ImGui::GetWindowDrawList();
        ImVec2 wp = ImGui::GetWindowPos();
        ImVec2 ws = ImGui::GetWindowSize();
        HP_DrawGlowPanel(dl, ImVec2(wp.x+4, wp.y+4), ImVec2(wp.x+ws.x-4, wp.y+ws.y-4), IM_COL32(55, 135, 255, 120), 13.0f);

        // Top center Healtracker banner/logo.
        // Image file expected at: MQ2HealParse\Images\Healtracker.png
        ImVec2 headerStart = ImGui::GetCursorScreenPos();
        float headerAvailW = ImGui::GetContentRegionAvail().x;
        const float headerH = 260.0f;
        const float logoMaxW = std::min(1800.0f, std::max(1200.0f, headerAvailW * 0.90f));
        const float logoMaxH = 240.0f;

        HP_LoadHealtrackerLogoTextureIfNeeded();
        if (g_healtrackerLogoTexture.id) {
            float texW = (float)std::max(1, g_healtrackerLogoTexture.width);
            float texH = (float)std::max(1, g_healtrackerLogoTexture.height);
            float scale = std::min(logoMaxW / texW, logoMaxH / texH);
            float drawW = texW * scale;
            float drawH = texH * scale;
            ImVec2 logoPos(headerStart.x + (headerAvailW - drawW) * 0.5f, headerStart.y + 4.0f);
            HP_DrawHealtrackerLogo(ImGui::GetWindowDrawList(), logoPos, logoMaxW, logoMaxH);
        }

        // Top-right credit/version text.
        const char* creditText = "Created by Dorfus | v5.0";
        ImVec2 creditSize = ImGui::CalcTextSize(creditText);
        ImGui::SetCursorScreenPos(ImVec2(headerStart.x + headerAvailW - creditSize.x - 10.0f, headerStart.y + 10.0f));
        ImGui::TextColored(ImVec4(0.72f, 0.84f, 1.0f, 0.92f), "%s", creditText);

        // Reserve the header area; old top-left HEALTRACKER text, swords icon,
        // and "- by Dorfus | V5.0" label were intentionally removed.
        ImGui::SetCursorScreenPos(ImVec2(headerStart.x, headerStart.y + headerH));

        // Align the main tabs below the centered logo.
        float hpTabStartX = std::max(240.0f, (headerAvailW - 520.0f) * 0.5f);
        ImGui::SetCursorPosX(hpTabStartX);
        HP_LoadHealsIconTextureIfNeeded();
        HP_LoadDpsIconTextureIfNeeded();
        HP_LoadSettingsIconTextureIfNeeded();

        HP_TabButton("HEALS", 0, IM_COL32(40, 150, 70, 255), &g_healsIconTexture); ImGui::SameLine();
        HP_TabButton("DPS", 1, IM_COL32(30, 110, 210, 255), &g_dpsIconTexture); ImGui::SameLine();
        HP_TabButton("SETTINGS", 4, IM_COL32(55, 75, 105, 255), &g_settingsIconTexture); ImGui::SameLine();
        if (HP_MiniGhostButton()) {
            g_liveOverlayEnabled.store(true);
            g_liveOverlayForceVisible.store(true);
            g_fullUiEnabled.store(false);
        }
        ImGui::Separator();

        int tab = g_fullUiTab.load();
        // History tab was removed because fights can now be searched directly from DPS and Heals.
        // Spells and Tank tabs were also folded into the DPS page.
        // If an old saved/session state still points to tab 2, 3, or 5, redirect it safely.
        if (tab == 2 || tab == 3) {
            tab = 1;
            g_fullUiTab.store(1);
        } else if (tab == 5) {
            tab = 4;
            g_fullUiTab.store(4);
        }
        float rightW = 320.0f;
        float leftW = ImGui::GetContentRegionAvail().x - rightW - 10.0f;
        // Keep the left fight selector style consistent, but each tab keeps its own data view.
        // Heals shows healing stats, DPS shows damage plus Spells & Burns and Tank Stats.
        if (tab == 0) HP_DrawHealsPageWithFightList(leftW, rightW);
        else if (tab == 1) HP_DrawDpsPage(leftW, rightW);
        else HP_DrawSettingsPage();

        ImGui::Separator();
        ImGui::TextDisabled("Parser: %s  |  LogTail: %s  |  Queue: %zu  |  Lines: %llu",
            g_enabled.load() ? "Running" : "Stopped",
            g_logTailEnabled.load() ? "On" : "Off",
            g_eventQueue.size(),
            (unsigned long long)g_linesSeen.load());
    }
    ImGui::End();
    HP_DrawCommandsWindow();
    HP_DrawPetOwnersWindow();
    HP_DrawBurnTimersWindow();
    HP_PopFullUiTheme();
    if (!open) g_fullUiEnabled.store(false);
}

void DrawHealParseFullUiOncePerFrame()
{
    static int lastFrame = -1;
    int frame = ImGui::GetFrameCount();
    if (frame == lastFrame) return;
    lastFrame = frame;
    DrawHealParseFullUi();
}

// MacroQuest builds have used different names for plugin ImGui callbacks across
// versions/distributions. Export both; the frame guard prevents duplicate draw
// if a build happens to call both in the same frame.
void DrawHealParseLiveDpsOverlayOncePerFrame()
{
    static int lastFrame = -1;
    int frame = ImGui::GetFrameCount();
    if (frame == lastFrame) return;
    lastFrame = frame;
    DrawHealParseLiveDpsOverlay();
}

void ClearLiveDpsIfMob(const std::string& mob)
{
    if (mob.empty()) return;
    std::lock_guard<std::mutex> lk(g_liveDpsMutex);
    if (g_liveDps.mob == mob) {
        HP_ArchiveLiveDpsLocked("kill");
        HP_ClearLiveDpsLocked();
    }
}

// Short duplicate guard for spell/non-melee damage. Some clients can expose the
// same spell damage through both a "hit ... non-melee" line and a
// "has taken ... damage from ... by ..." line. GamParse counts one damage
// event; without this guard HealTracker can run high. Melee is intentionally
// excluded because identical melee hit amounts can legitimately repeat quickly.
std::unordered_map<std::string, int64_t> g_recentSpellDamageKeys;
std::mutex g_recentSpellDamageMutex;
constexpr int64_t kSpellDamageDedupMs = 1200;

bool ShouldDropRecentSpellDamage(const std::string& attacker,
                                 const std::string& target,
                                 const std::string& type,
                                 uint64_t amount) {
    if (!g_spellDamageDedupEnabled.load()) return false;
    if (type == "melee") return false;
    if (attacker.empty() || target.empty() || amount == 0) return false;

    const int64_t now = NowMs();
    const std::string key = attacker + "" + target + "" + type + "" + std::to_string(amount);

    std::lock_guard<std::mutex> lk(g_recentSpellDamageMutex);
    auto it = g_recentSpellDamageKeys.find(key);
    if (it != g_recentSpellDamageKeys.end() && (now - it->second) >= 0 && (now - it->second) < kSpellDamageDedupMs) {
        it->second = now;
        return true;
    }
    g_recentSpellDamageKeys[key] = now;

    if (g_recentSpellDamageKeys.size() > 4096) {
        for (auto p = g_recentSpellDamageKeys.begin(); p != g_recentSpellDamageKeys.end(); ) {
            if ((now - p->second) > 5000) p = g_recentSpellDamageKeys.erase(p);
            else ++p;
        }
    }
    return false;
}

static std::string KvFromBatch(const DamageBatchStats& b) {
    std::string attacker = b.attacker;
    std::string target = b.target;
    std::string type = b.type;
    EscapeEventValue(attacker);
    EscapeEventValue(target);
    EscapeEventValue(type);
    std::string line("damage_batch");
    line += "|attacker="; line += attacker;
    line += "|target=";   line += target;
    line += "|amount=";   line += std::to_string(b.amount);
    line += "|type=";     line += type;
    line += "|max=";      line += std::to_string(b.maxHit);
    line += "|count=";    line += std::to_string(b.count);
    return line;
}

void FlushDamageBatch(bool force = false) {
    if (!g_pushToLua.load()) return;
    const int64_t now = NowMs();
    if (!force && g_lastDamageBatchFlushMs != 0 && (now - g_lastDamageBatchFlushMs) < kDamageBatchFlushMs)
        return;

    std::vector<std::string> lines;
    {
        std::lock_guard<std::mutex> lk(g_damageBatchMutex);
        if (g_damageBatch.empty()) return;
        lines.reserve(g_damageBatchOrder.size());
        for (const auto& key : g_damageBatchOrder) {
            auto it = g_damageBatch.find(key);
            if (it != g_damageBatch.end() && it->second.amount > 0)
                lines.emplace_back(KvFromBatch(it->second));
        }
        g_damageBatch.clear();
        g_damageBatchOrder.clear();
        g_lastDamageBatchFlushMs = now;
    }

    for (auto& line : lines) {
        EnqueueEvent(std::move(line));
        g_eventsPosted.fetch_add(1, std::memory_order_relaxed);
    }
}

static bool HP_ShouldDropDamageForActiveFightTarget(const std::string& attacker,
                                                    const std::string& target,
                                                    uint64_t amount,
                                                    const std::string& type,
                                                    const std::string& spell)
{
    if (target.empty()) return false;

    std::lock_guard<std::mutex> lk(g_liveDpsMutex);
    if (g_liveDps.mob.empty() || g_liveDps.total == 0) return false;

    // Do not let rain/AE/add damage get batched into the selected mob fight.
    // This is what was inflating Eyehop/Ihopp/Longhorn compared to GamParse:
    // the active fight was "a goblin worker", but rain lines also hit
    // "an iron warder" and "a granite defender".
    if (!HP_SameNameNoCase(target, g_liveDps.mob)) {
        HP_AuditLine("DROP", attacker, HP_GetLinkedPetOwnerForDisplay(attacker), target, amount, type, spell, "off-target-active-fight");
        return true;
    }
    return false;
}

bool TryBatchDamageEvent(std::initializer_list<std::pair<const char*, std::string>> kvs) {
    std::string attacker, target, type, spell;
    uint64_t amount = 0;
    uint32_t maxHit = 0;

    for (auto& kv : kvs) {
        if (std::strcmp(kv.first, "attacker") == 0) attacker = kv.second;
        else if (std::strcmp(kv.first, "target") == 0) target = kv.second;
        else if (std::strcmp(kv.first, "type") == 0) type = kv.second;
        else if (std::strcmp(kv.first, "spell") == 0) spell = kv.second;
        else if (std::strcmp(kv.first, "amount") == 0) amount = std::strtoull(kv.second.c_str(), nullptr, 10);
        else if (std::strcmp(kv.first, "max") == 0) maxHit = (uint32_t)std::strtoul(kv.second.c_str(), nullptr, 10);
    }

    if (amount == 0 || attacker.empty() || target.empty()) return false;
    if (type.empty()) type = "melee";
    if (maxHit == 0 || maxHit > amount) maxHit = (uint32_t)((amount > UINT32_MAX) ? UINT32_MAX : amount);

    // Match GamParse selected-fight behavior: once a main mob is active, do not
    // count rain/AE hits on nearby adds inside that mob's fight.
    if (HP_ShouldDropDamageForActiveFightTarget(attacker, target, amount, type, spell)) {
        return true;
    }

    // Consume duplicate spell/non-melee damage lines before they reach Lua only
    // when explicitly enabled. By default we count the final log events exactly
    // like GamParse.
    if (ShouldDropRecentSpellDamage(attacker, target, type, amount)) {
        HP_AuditLine("DROP", attacker, HP_GetLinkedPetOwnerForDisplay(attacker), target, amount, type, spell, "spell-dedup");
        return true;
    }
    HP_AuditLine("COUNT", attacker, HP_GetLinkedPetOwnerForDisplay(attacker), target, amount, type, spell, "batched");

    const std::string key = attacker + "\x1f" + target + "\x1f" + type;
    {
        std::lock_guard<std::mutex> lk(g_damageBatchMutex);
        auto it = g_damageBatch.find(key);
        if (it == g_damageBatch.end()) {
            DamageBatchStats b;
            b.attacker = attacker;
            b.target = target;
            b.type = type;
            it = g_damageBatch.emplace(key, std::move(b)).first;
            g_damageBatchOrder.emplace_back(key);
        }
        auto& b = it->second;
        b.amount += amount;
        b.count += 1;
        if (maxHit > b.maxHit) b.maxHit = maxHit;
    }

    FlushDamageBatch(false);
    return true;
}

// PostEvent enqueues a single non-damage event for the bridge to drain. Damage
// events are batched above and emitted as damage_batch rows.
void PostEvent(const char* kind,
               std::initializer_list<std::pair<const char*, std::string>> kvs) {
    // The plugin-owned live DPS overlay must update from the plugin parse path
    // even when Lua forwarding is disabled or the Lua bridge is not draining.
    // The previous plugin-ImGui build drew the window, but live fights stayed
    // at "Waiting for combat" because only the Lua batch queue was updated.
    if (kind && std::strcmp(kind, "damage") == 0) {
        std::string liveAttacker, liveTarget, liveType;
        uint64_t liveAmount = 0;
        uint32_t liveMax = 0;
        for (auto& kv : kvs) {
            if (std::strcmp(kv.first, "attacker") == 0) liveAttacker = kv.second;
            else if (std::strcmp(kv.first, "target") == 0) liveTarget = kv.second;
            else if (std::strcmp(kv.first, "amount") == 0) liveAmount = std::strtoull(kv.second.c_str(), nullptr, 10);
            else if (std::strcmp(kv.first, "max") == 0) liveMax = (uint32_t)std::strtoul(kv.second.c_str(), nullptr, 10);
            else if (std::strcmp(kv.first, "type") == 0) liveType = kv.second;
        }
        if (liveMax == 0 || liveMax > liveAmount)
            liveMax = (uint32_t)((liveAmount > UINT32_MAX) ? UINT32_MAX : liveAmount);
        if (liveType.empty()) liveType = "melee";
        NoteLiveDamage(liveAttacker, liveTarget, liveAmount, liveMax, liveType);
    }

    if (kind && std::strcmp(kind, "incoming") == 0) {
        std::string t, attacker, type, verb, spell; uint64_t amt = 0;
        for (auto& kv : kvs) {
            if (std::strcmp(kv.first, "target") == 0) t = kv.second;
            else if (std::strcmp(kv.first, "attacker") == 0) attacker = kv.second;
            else if (std::strcmp(kv.first, "type") == 0) type = kv.second;
            else if (std::strcmp(kv.first, "verb") == 0) verb = kv.second;
            else if (std::strcmp(kv.first, "spell") == 0) spell = kv.second;
            else if (std::strcmp(kv.first, "amount") == 0) amt = std::strtoull(kv.second.c_str(), nullptr, 10);
        }
        std::string hitType = !spell.empty() ? spell : (!verb.empty() ? verb : (!type.empty() ? type : std::string("Hit")));
        NoteLiveIncoming(t, amt, attacker, hitType);
    } else if (kind && std::strcmp(kind, "avoid") == 0) {
        std::string t, k;
        for (auto& kv : kvs) {
            if (std::strcmp(kv.first, "target") == 0) t = kv.second;
            else if (std::strcmp(kv.first, "kind") == 0) k = kv.second;
        }
        NoteLiveAvoid(t, k);
    }

    if (!g_pushToLua.load()) return;

    if (kind && std::strcmp(kind, "damage") == 0) {
        if (TryBatchDamageEvent(kvs)) return;
        // If a malformed damage event cannot be batched, fall through and send it raw.
    } else {
        FlushDamageBatch(true);
    }

    std::string line(kind);
    for (auto& kv : kvs) {
        std::string v = kv.second;
        EscapeEventValue(v);
        line += '|';
        line += kv.first;
        line += '=';
        line += v;
    }

    EnqueueEvent(std::move(line));
    g_eventsPosted.fetch_add(1, std::memory_order_relaxed);
}

// ----------------------------------------------------------------------------
// Internal aggregation. Each parse routine calls these to update the maps the
// TLO exposes. The bridge separately gets the same data via PostEvent and
// runs it through the existing Lua aggregator.
// ----------------------------------------------------------------------------

std::string LookupSpellCaster(const std::string& spell);

static std::string HP_DisplayHealerForHeal(const std::string& target, const std::string& healer, const std::string& spellOverride, std::string& outSpell, std::string& outType)
{
    std::string h = healer.empty() ? target : healer;
    outSpell = spellOverride.empty() ? (healer.empty() ? "Direct Heals" : healer) : spellOverride;
    outType = "Heal";

    // HoT / regen heals should count under the caster, but the spell itself
    // should be grouped into the HoT / Regen bucket in the Heals tab.
    if (!spellOverride.empty() && HP_IsHotRegenHealName(spellOverride)) {
        outSpell = spellOverride;
        outType = "HoT / Regen";
        return h;
    }

    std::string hl = LowerCopy(healer);
    if (hl == "self-proc" || hl.find("self-proc") != std::string::npos) {
        outSpell = "self-proc";
        outType = "Proc Heal";
        return target.empty() ? healer : target;
    }

    if (hl.find("aspect of survival") != std::string::npos) {
        outSpell = "Aspect of Survival";
        outType = "Rune";
        std::string caster = LookupSpellCaster("Aspect of Survival");
        return caster.empty() ? (target.empty() ? healer : target) : caster;
    }
    if (hl.find("rune of rikk") != std::string::npos) {
        outSpell = "Rune of Rikkukin";
        outType = "Rune";
        std::string caster = LookupSpellCaster("Rune of Rikkukin");
        if (caster.empty()) caster = LookupSpellCaster("Rune of Rikkikun");
        return caster.empty() ? (target.empty() ? healer : target) : caster;
    }
    if (hl.find("glyph") != std::string::npos) {
        outSpell = healer;
        outType = "Rune";
        std::string caster = LookupSpellCaster(healer);
        return caster.empty() ? (target.empty() ? healer : target) : caster;
    }
    if (hl.find("rune") != std::string::npos || hl.find("shield") != std::string::npos) {
        outSpell = healer;
        outType = "Rune";
        std::string caster = LookupSpellCaster(healer);
        return caster.empty() ? (target.empty() ? healer : target) : caster;
    }

    outSpell = "Direct Heals";
    outType = "Heal";
    return h;
}

void BumpHeal(const std::string& target, const std::string& healer, uint32_t amount, const std::string& spellOverride = std::string()) {
    std::string spellName;
    std::string healType;
    std::string displayHealer = HP_DisplayHealerForHeal(target, healer, spellOverride, spellName, healType);

    {
        std::lock_guard<std::mutex> lk(g_statsMutex);
        auto& t = g_healByTarget[target];
        t.total += amount;
        t.count += 1;
        if (amount > t.max) t.max = amount;
        auto& h = t.healers[displayHealer];
        h.total += amount;
        h.count += 1;
        if (amount > h.max) h.max = amount;
    }
    // Live HPS leaderboard (separate mutex, kept outside g_statsMutex).
    NoteLiveHeal(target, displayHealer, spellName, healType, amount);
}

void BumpDamage(const std::string& attacker, uint32_t amount) {
    std::lock_guard<std::mutex> lk(g_statsMutex);
    auto& a = g_damageByAttacker[attacker];
    a.total += amount;
    a.count += 1;
    if (amount > a.max) a.max = amount;
}

void NoteKnownChar(const std::string& name) {
    if (name.empty()) return;
    std::lock_guard<std::mutex> lk(g_statsMutex);
    g_knownChars.insert(name);
}

void RememberSpellCast(const std::string& spell, const std::string& caster) {
    if (spell.empty() || caster.empty()) return;
    int64_t now = NowMs();
    {
        std::lock_guard<std::mutex> lk(g_statsMutex);
        g_recentSpellCasts[spell] = RecentCast{ caster, now };
        g_spellCastsByCaster[caster] += 1;
        g_spellCastsBySpell[spell] += 1;
        // Bound the cache.
        if (g_recentSpellCasts.size() > 4096) {
            for (auto it = g_recentSpellCasts.begin(); it != g_recentSpellCasts.end();) {
                if (now - it->second.atMs > 60000) it = g_recentSpellCasts.erase(it);
                else ++it;
            }
        }
    }

    // Save spell casts to the current DPS fight only.  If the spell cast line
    // arrives a split second before the first damage line starts the encounter,
    // keep it briefly and attach it when that fight opens.
    HP_RecordLiveDpsSpellCast(caster, spell);
    {
        std::lock_guard<std::mutex> pk(g_pendingDpsSpellMutex);
        g_pendingDpsSpellCasts.push_back({ HP_TrimCopy(caster), HP_TrimCopy(spell), now });
        for (auto it = g_pendingDpsSpellCasts.begin(); it != g_pendingDpsSpellCasts.end();) {
            if ((now - it->ms) > 15000) it = g_pendingDpsSpellCasts.erase(it);
            else ++it;
        }
        if (g_pendingDpsSpellCasts.size() > 200)
            g_pendingDpsSpellCasts.erase(g_pendingDpsSpellCasts.begin(), g_pendingDpsSpellCasts.begin() + (g_pendingDpsSpellCasts.size() - 200));
    }
}

std::string LookupSpellCaster(const std::string& spell) {
    std::lock_guard<std::mutex> lk(g_statsMutex);
    auto it = g_recentSpellCasts.find(spell);
    if (it != g_recentSpellCasts.end()) return it->second.caster;

    // Rune names in fade/absorb messages are sometimes slightly different
    // from the actual cast name. Match loosely so receiver totals credit the
    // caster instead of creating fake healer rows such as "Rune of Rikkukin".
    std::string want = LowerCopy(spell);
    Trim(want);
    if (want.find("aspect of survival") != std::string::npos) want = "aspect of survival";
    else if (want.find("rikkukin") != std::string::npos) want = "rikkukin";
    else if (want.find("glyph spray") != std::string::npos || want.find("glyph") != std::string::npos) want = "glyph";

    int64_t now = NowMs();
    std::string bestCaster;
    int64_t bestAge = 600000;
    for (const auto& kv : g_recentSpellCasts) {
        std::string have = LowerCopy(kv.first);
        Trim(have);
        bool match = false;
        if (!want.empty() && have.find(want) != std::string::npos) match = true;
        if (!match && want == "rikkukin" && have.find("rikkukin") != std::string::npos) match = true;
        if (!match) continue;
        int64_t age = now - kv.second.atMs;
        if (age >= 0 && age < bestAge) { bestAge = age; bestCaster = kv.second.caster; }
    }
    return bestCaster;
}

// ----------------------------------------------------------------------------
// Parsers. Each returns true if it consumed the line.
// ----------------------------------------------------------------------------

// "<healer> has healed you for N (M) hit points." / "...point of damage."
//   captures: healer, amount, target=YOU
bool ParseHealIn(const char* line, const std::string& myName) {
    // Quick reject.
    const char* p = FindSubstr(line, " has healed you for ");
    if (!p) return false;

    // Healer = chars before " has healed you for "
    std::string healer(line, p - line);
    Trim(healer);
    healer = HP_NormalizeHealCasterName(healer);
    if (healer.empty()) return false;

    const char* rest = p + std::strlen(" has healed you for ");
    uint64_t amount = 0;
    const char* after = nullptr;
    if (!ParseUintWithCommas(rest, &amount, &after)) return false;
    if (amount == 0) return false;

    // Verify it's a heal line, not something weirdly truncated.
    if (!FindSubstr(after, "point")) return false;

    std::string spellName = HP_ExtractHealSpellFromTail(after);
    BumpHeal(myName, healer, (uint32_t)amount, spellName);
    NoteKnownChar(healer);

    char amtBuf[32];
    std::snprintf(amtBuf, sizeof(amtBuf), "%llu", (unsigned long long)amount);
    PostEvent("heal",
              { {"target", myName},
                {"healer", healer},
                {"amount", amtBuf} });
    return true;
}

// "<healer> healed you for N hit points by <Spell>."
// Project Lazarus HoT examples:
//   "Dorias healed you for 1912 hit points by Pious Elixir."
//   "Dorias healed you for 3480 hit points by Celestial Regeneration."
bool ParseHealInNoHas(const char* line, const std::string& myName) {
    const char* p = FindSubstr(line, " healed you for ");
    if (!p) return false;

    std::string healer(line, p - line);
    Trim(healer);
    if (healer.empty()) return false;

    const char* rest = p + std::strlen(" healed you for ");
    uint64_t amount = 0;
    const char* after = nullptr;
    if (!ParseUintWithCommas(rest, &amount, &after)) return false;
    if (amount == 0) return false;
    if (!FindSubstr(after, "point")) return false;

    std::string spellName = HP_ExtractHealSpellFromTail(after);
    BumpHeal(myName, healer, (uint32_t)amount, spellName);
    NoteKnownChar(healer);

    char amtBuf[32];
    std::snprintf(amtBuf, sizeof(amtBuf), "%llu", (unsigned long long)amount);
    PostEvent("heal",
              { {"target", myName},
                {"healer", healer},
                {"amount", amtBuf},
                {"spell", spellName} });
    return true;
}


// "<healer> healed <target> for N hit points by <Spell>."
// "<healer> has healed <target> for N hit points."
// This catches visible heals on other players so HEALED FOR can show everyone
// who received healing, not just the local character receiving "you" heals.
bool ParseHealOtherTarget(const char* line, const std::string& myName) {
    const char* p = FindSubstr(line, " healed ");
    const char* sep = " healed ";
    if (!p) { p = FindSubstr(line, " has healed "); sep = " has healed "; }
    if (!p) return false;

    // Do not steal the explicit "you" handlers; they normalize target to myName.
    if (FindSubstr(line, " healed you for ") || FindSubstr(line, " has healed you for "))
        return false;

    // Do not let the generic parser turn "You have healed Target..." into
    // healer="You have". The self-cast parser below credits the actual player.
    if (StartsWith(line, "You have healed "))
        return false;

    std::string healer(line, p - line);
    Trim(healer);
    if (healer.empty()) return false;

    const char* targetStart = p + std::strlen(sep);
    const char* forp = FindSubstr(targetStart, " for ");
    if (!forp) return false;

    std::string target(targetStart, forp - targetStart);
    Trim(target);
    if (target.empty()) return false;

    // Ignore messages where the "target" fragment is not a player name.
    std::string tl = LowerCopy(target);
    if (tl == "you" || tl.find("hit point") != std::string::npos || tl.find("point") != std::string::npos)
        return false;

    const char* rest = forp + 5;
    uint64_t amount = 0;
    const char* after = nullptr;
    if (!ParseUintWithCommas(rest, &amount, &after)) return false;
    if (amount == 0) return false;
    if (!FindSubstr(after, "point")) return false;

    std::string spellName = HP_ExtractHealSpellFromTail(after);
    BumpHeal(target, healer, (uint32_t)amount, spellName);
    NoteKnownChar(healer);
    NoteKnownChar(target);

    char amtBuf[32];
    std::snprintf(amtBuf, sizeof(amtBuf), "%llu", (unsigned long long)amount);
    PostEvent("heal",
              { {"target", target},
                {"healer", healer},
                {"amount", amtBuf},
                {"spell", spellName} });
    return true;
}

// "You have been healed by <healer> for N hit points."
//   alt form -- some servers/spells emit this instead of basic.
bool ParseHealInAlt(const char* line, const std::string& myName) {
    if (!StartsWith(line, "You have been healed by ")) return false;
    const char* p = line + std::strlen("You have been healed by ");
    const char* forp = FindSubstr(p, " for ");
    if (!forp) return false;
    std::string healer(p, forp - p);
    Trim(healer);
    if (healer.empty()) return false;
    const char* rest = forp + 5;
    uint64_t amount = 0;
    const char* after = nullptr;
    if (!ParseUintWithCommas(rest, &amount, &after)) return false;
    if (amount == 0) return false;
    std::string spellName = HP_ExtractHealSpellFromTail(after);
    BumpHeal(myName, healer, (uint32_t)amount, spellName);
    NoteKnownChar(healer);
    char amtBuf[32];
    std::snprintf(amtBuf, sizeof(amtBuf), "%llu", (unsigned long long)amount);
    PostEvent("heal",
              { {"target", myName},
                {"healer", healer},
                {"amount", amtBuf},
                {"spell", spellName} });
    return true;
}

// "You have been healed for N hit points by your <Effect>."  (self-proc)
bool ParseHealSelfProc(const char* line, const std::string& myName) {
    if (!StartsWith(line, "You have been healed for ")) return false;
    const char* p = line + std::strlen("You have been healed for ");
    uint64_t amount = 0;
    const char* after = nullptr;
    if (!ParseUintWithCommas(p, &amount, &after)) return false;
    if (!FindSubstr(after, "by your ")) return false;
    BumpHeal(myName, "self-proc", (uint32_t)amount);
    char amtBuf[32];
    std::snprintf(amtBuf, sizeof(amtBuf), "%llu", (unsigned long long)amount);
    PostEvent("heal",
              { {"target", myName},
                {"healer", std::string("self-proc")},
                {"amount", amtBuf} });
    return true;
}

// "You have healed <target> for N points." -- credit your character and keep the real healed target.
bool ParseHealSelfCast(const char* line, const std::string& myName) {
    if (!StartsWith(line, "You have healed ")) return false;
    const char* p = line + std::strlen("You have healed ");
    const char* forp = FindSubstr(p, " for ");
    if (!forp) return false;
    std::string target(p, forp - p);
    Trim(target);
    if (target.empty()) return false;
    const char* rest = forp + 5;
    uint64_t amount = 0;
    const char* after = nullptr;
    if (!ParseUintWithCommas(rest, &amount, &after)) return false;
    if (amount == 0) return false;
    std::string spellName = HP_ExtractHealSpellFromTail(after);
    BumpHeal(target, myName, (uint32_t)amount, spellName);
    NoteKnownChar(target);
    char amtBuf[32];
    std::snprintf(amtBuf, sizeof(amtBuf), "%llu", (unsigned long long)amount);
    PostEvent("heal",
              { {"target", target},
                {"healer", myName},
                {"amount", amtBuf},
                {"spell", spellName} });
    return true;
}

// Rune absorbs -- fixed-amount heal credit, per-class.
static std::string HP_ExtractRuneReceiver(const char* line, const char* marker, const std::string& myName)
{
    if (!line || !marker) return myName;
    const char* p = FindSubstr(line, marker);
    if (!p) return myName;
    p += std::strlen(marker);
    while (*p == ' ' || *p == '\t') ++p;
    std::string target(p);
    Trim(target);
    while (!target.empty() && (target.back() == '.' || target.back() == '!' || target.back() == ','))
        target.pop_back();
    Trim(target);
    if (target.empty()) return myName;
    std::string tl = LowerCopy(target);
    if (tl == "you" || tl == "yourself") return myName;
    // Trim common trailing phrases that can appear in buff/fade text.
    const char* cuts[] = { " from ", " as ", " with ", " for ", " fades", " fade" };
    for (const char* c : cuts) {
        size_t pos = LowerCopy(target).find(c);
        if (pos != std::string::npos) { target.erase(pos); Trim(target); }
    }
    return target.empty() ? myName : target;
}

bool ParseHealRune(const char* line, const std::string& myName) {
    if (FindSubstr(line, "An aspect of survival shields you")) {
        BumpHeal(myName, "Aspect of Survival Rune", 1500);
        PostEvent("heal", { {"target", myName}, {"healer", std::string("Aspect of Survival Rune")}, {"amount", std::string("1500")} });
        return true;
    }
    if (FindSubstr(line, "An aspect of survival shields ")) {
        std::string target = HP_ExtractRuneReceiver(line, "An aspect of survival shields ", myName);
        BumpHeal(target, "Aspect of Survival Rune", 1500);
        NoteKnownChar(target);
        PostEvent("heal", { {"target", target}, {"healer", std::string("Aspect of Survival Rune")}, {"amount", std::string("1500")} });
        return true;
    }
    if (FindSubstr(line, "The platinum scales fade")) {
        std::string target = myName;
        if (FindSubstr(line, " from ")) target = HP_ExtractRuneReceiver(line, " from ", myName);
        BumpHeal(target, "Rune of Rikkukin", 2100);
        NoteKnownChar(target);
        PostEvent("heal", { {"target", target}, {"healer", std::string("Rune of Rikkukin")}, {"amount", std::string("2100")} });
        return true;
    }
    if (FindSubstr(line, "The shimmer of runes fades")) {
        std::string target = myName;
        if (FindSubstr(line, " from ")) target = HP_ExtractRuneReceiver(line, " from ", myName);
        BumpHeal(target, "Glyph Spray", 10000);
        NoteKnownChar(target);
        PostEvent("heal", { {"target", target}, {"healer", std::string("Glyph Spray")}, {"amount", std::string("10000")} });
        return true;
    }
    return false;
}

// "<caster> begins to cast a spell. <Spell>"  or  "You begin casting <Spell>."
bool ParseSpellCast(const char* line, const std::string& myName) {
    const char* p = FindSubstr(line, " begins to cast a spell");
    if (p) {
        std::string caster(line, p - line);
        Trim(caster);
        // Pet casts -- attribute to owner.
        size_t apos = std::string::npos;
        for (size_t i = 0; i + 4 < caster.size(); ++i) {
            if ((caster[i] == '`' || caster[i] == '\'')
                && caster[i + 1] == 's' && caster[i + 2] == ' '
                && caster[i + 3] == 'p' && caster[i + 4] == 'e') {
                apos = i; break;
            }
        }
        if (apos != std::string::npos) caster = caster.substr(0, apos);

        // Spell is between < and >.
        const char* lt = std::strchr(p, '<');
        if (!lt) return false;
        const char* gt = std::strchr(lt, '>');
        if (!gt) return false;
        std::string spell(lt + 1, gt - lt - 1);
        Trim(spell);

        if (!caster.empty() && !spell.empty()) {
            RememberSpellCast(spell, caster);
            NoteKnownChar(caster);
            PostEvent("spell_cast", { {"caster", caster}, {"spell", spell} });
        }
        return true;
    }
    if (StartsWith(line, "You begin casting ")) {
        std::string spell(line + std::strlen("You begin casting "));
        // Trim trailing "."
        while (!spell.empty() && (spell.back() == '.' || spell.back() == ' '))
            spell.pop_back();
        if (!spell.empty()) {
            RememberSpellCast(spell, myName);
            PostEvent("spell_cast", { {"caster", myName}, {"spell", spell} });
        }
        return true;
    }
    return false;
}

// "You have slain <mob>!"  or  "<mob> has been slain by <slayer>!"
//
// In a 54-man raid, the killing blow usually comes from someone other than
// the driver, so most kill lines are the "<mob> has been slain by <slayer>"
// form. Previous versions of this function had aggressive PC-detection
// filters on the slain side (g_knownChars lookup + synchronous Spawn TLO),
// and a false-positive in either would silently swallow every kill of that
// mob name forever. The result was a kill counter that stuck at 2-3 events
// instead of incrementing on each pull.
//
// New approach: do minimal filtering. The only real false positives are
// (a) you yourself dying, (b) a pet dying, (c) a known player dying. The
// first two are unambiguous from the line text. The third is covered by
// the simple knownChars contains-name check below -- but ONLY exact-match,
// no fuzzy stuff. If a name is in knownChars it's a confirmed player
// (added when we saw them heal or attack), so it's safe to filter.
// We deliberately do NOT call any TLO lookups here.
bool ParseKill(const char* line, const std::string& myName) {
    if (StartsWith(line, "You have slain ")) {
        std::string mob(line + std::strlen("You have slain "));
        while (!mob.empty() && (mob.back() == '!' || mob.back() == ' ' || mob.back() == '.'))
            mob.pop_back();
        if (!mob.empty()) {
            // Suppress kills for charmed-only pets so they don't open
            // phantom fight scopes on the Lua side. If a hostile spawn
            // of the same name also exists, keep the event.
            if (HasOnlyCharmedSpawn(mob)) {
                if (g_debug.load()) {
                    WriteChatf("\ag[HealParse]\ax kill suppressed: charmed-only '%s'", mob.c_str());
                }
                return true;
            }
            ClearLiveDpsIfMob(mob);
            PostEvent("kill", { {"mob", mob}, {"from", myName} });
        }
        return true;
    }
    const char* p = FindSubstr(line, " has been slain by ");
    if (p) {
        std::string slain(line, p - line);
        Trim(slain);
        if (slain.empty()) return true;

        // Filter 1: it is you / the driver. Count it as a PC death for the active fight.
        if (slain == "You" || slain == "you" || slain == myName) {
            std::string killer(p + std::strlen(" has been slain by "));
            while (!killer.empty() && (killer.back() == '!' || killer.back() == '.' || killer.back() == ' '))
                killer.pop_back();
            Trim(killer);
            HP_NotePcDeath(myName, killer);
            return true;
        }

        // Filter 2: pet/ward/swarm/doppelganger death (substring match on
        // the possessive form -- pets are always "<owner>`s pet" etc).
        if (slain.find("`s pet")          != std::string::npos
            || slain.find("'s pet")        != std::string::npos
            || slain.find("`s warder")     != std::string::npos
            || slain.find("'s warder")     != std::string::npos
            || slain.find("`s ward")       != std::string::npos
            || slain.find("'s ward")       != std::string::npos
            || slain.find("`s swarm")      != std::string::npos
            || slain.find("'s swarm")      != std::string::npos
            || slain.find("`s doppelganger") != std::string::npos
            || slain.find("'s doppelganger") != std::string::npos
            || slain.find("animated corpse") != std::string::npos) {
            return true;
        }

        // Filter 3: confirmed player (only via exact match in g_knownChars,
        // which is only populated when we've already seen the name HEAL or
        // ATTACK -- so it's a strong signal). We deliberately do NOT do a
        // case-insensitive scan -- mob names can sometimes share letters
        // with player names and we'd rather over-report a kill than drop
        // a legitimate mob kill.
        {
            std::lock_guard<std::mutex> lk(g_statsMutex);
            if (g_knownChars.count(slain)) {
                std::string killer(p + std::strlen(" has been slain by "));
                while (!killer.empty() && (killer.back() == '!' || killer.back() == '.' || killer.back() == ' '))
                    killer.pop_back();
                Trim(killer);
                HP_NotePcDeath(slain, killer);
                return true;
            }
        }

        {
            std::lock_guard<std::mutex> dlk(g_liveDpsMutex);
            if (HP_LiveDpsHasPlayerNoLock(slain)) {
                std::string killer(p + std::strlen(" has been slain by "));
                while (!killer.empty() && (killer.back() == '!' || killer.back() == '.' || killer.back() == ' '))
                    killer.pop_back();
                Trim(killer);
                // Release lock before calling note helper by doing the insert directly.
                bool duplicate = false;
                int64_t now = NowMs();
                for (const auto& d : g_liveDps.deaths) {
                    if (d.player == slain && (now - d.ms) >= 0 && (now - d.ms) < 2500) { duplicate = true; break; }
                }
                if (!duplicate) {
                    HPPcDeathRow d; d.player = slain; d.killer = killer.empty() ? g_liveDps.mob : killer; d.ms = now; d.wall = HP_WallNow();
                    g_liveDps.deaths.push_back(d);
                }
                return true;
            }
        }

        // Suppress kills for charmed-only pets (charmed mob died but no
        // hostile counterpart exists). Avoids creating phantom fight
        // scopes on the Lua side.
        if (HasOnlyCharmedSpawn(slain)) {
            if (g_debug.load()) {
                WriteChatf("\ag[HealParse]\ax kill suppressed: charmed-only '%s'", slain.c_str());
            }
            return true;
        }

        // Anything else is treated as a mob kill. Emit the event.
        ClearLiveDpsIfMob(slain);
        PostEvent("kill", { {"mob", slain}, {"from", myName} });
        return true;
    }
    return false;
}

// "<target> has taken <N> damage from <X> by <Y>."  -- spell damage
// "<target> has taken <N> damage from your <Spell>."
// "<target> has taken <N> damage from <Spell>."     -- anonymous DoT tick
bool ParseSpellDamage(const char* line, const std::string& myName) {
    const char* taken = FindSubstr(line, " has taken ");
    if (!taken) return false;

    std::string target(line, taken - line);
    Trim(target);
    if (target.empty()) return false;

    // Drop mob -> player.
    if (target == "YOU" || target == "you" || target == myName) return true;
    {
        std::lock_guard<std::mutex> lk(g_statsMutex);
        if (g_knownChars.count(target)) return true;
    }

    // Charm-target drop. Only drop if EVERY same-named spawn is a charmed
    // pet. If a hostile counterpart also exists in zone, keep the event -
    // we'd rather record a couple of phantom hits on the charmed pet than
    // miss a real hostile fight scope.
    if (HasOnlyCharmedSpawn(target)) {
        return true;
    }

    const char* p = taken + std::strlen(" has taken ");
    uint64_t amount = 0;
    const char* after = nullptr;
    if (!ParseUintWithCommas(p, &amount, &after)) return false;
    if (amount == 0) return false;

    // Confirm "damage from " comes next.
    if (!StartsWith(after, " damage from ")) return false;
    const char* mid_start = after + std::strlen(" damage from ");

    // Three sub-forms.
    //   form A: "<spell> by <caster>."
    //   form B: "your <spell>."
    //   form C: "<spell>." (anonymous DoT)

    if (StartsWith(mid_start, "your ")) {
        std::string spell(mid_start + 5);
        while (!spell.empty() && (spell.back() == '.' || spell.back() == ' '))
            spell.pop_back();
        BumpDamage(myName, (uint32_t)amount);
        char amtBuf[32];
        std::snprintf(amtBuf, sizeof(amtBuf), "%llu", (unsigned long long)amount);
        const char* dmgKind = IsNecroDotSpell(spell) ? "dot" : "spell";
        PostEvent("damage",
                  { {"attacker", myName},
                    {"target", target},
                    {"amount", amtBuf},
                    {"count", std::string("1")},
                    {"max", amtBuf},
                    {"type", std::string(dmgKind)},
                    {"spell", spell} });
        return true;
    }

    const char* byp = FindSubstr(mid_start, " by ");
    if (byp) {
        std::string mid(mid_start, byp - mid_start);
        std::string last(byp + 4);
        while (!last.empty() && (last.back() == '.' || last.back() == ' '))
            last.pop_back();
        Trim(mid);

        // Disambiguate which capture is the caster vs the spell name.
        std::string caster;
        bool midPc = false, lastPc = false;
        {
            std::lock_guard<std::mutex> lk(g_statsMutex);
            midPc = g_knownChars.count(mid) > 0 || IsKnownPet(mid);
            lastPc = g_knownChars.count(last) > 0 || IsKnownPet(last);
        }
        if (midPc) caster = mid;
        else if (lastPc) caster = last;
        else if (!LookupSpellCaster(mid).empty()) caster = last;
        else if (!LookupSpellCaster(last).empty()) caster = mid;
        else if (LooksLikePcName(mid) && !LooksLikePcName(last)) caster = mid;
        else if (LooksLikePcName(last) && !LooksLikePcName(mid)) caster = last;
        else if (LooksLikePcName(mid)) caster = mid;
        else caster = mid; // last resort, match the Lua's behavior

        if (caster.empty()) return true;
        if (LooksLikePcName(caster)) NoteKnownChar(caster);

        // Determine the spell name in lines like:
        //   <mob> has taken N damage from Screamz by Night Fire.
        //   <mob> has taken N damage from Mind Shatter by Screamz.
        // If caster is the first side, the second side is the spell.
        // If caster is the second side, the first side is the spell.
        std::string spellName = (caster == mid) ? last : mid;
        Trim(spellName);

        std::string owner = ResolveAttacker(caster);
        BumpDamage(owner, (uint32_t)amount);
        char amtBuf[32];
        std::snprintf(amtBuf, sizeof(amtBuf), "%llu", (unsigned long long)amount);
        const char* dmgKind = IsNecroDotSpell(spellName) ? "dot" : "spell";

        // DOT DEBUG:
        // Turn on with: /healparse debug on
        // This shows whether the parser is reading:
        //   caster = Screamz
        //   spell  = Chaos Plague / Pyre of Mori / Blood of Thule
        // If caster and spell are backwards here, the plugin will classify DoTs as spell damage.
        if (g_debug.load()) {
            WriteChatf(
                "\ay[DOTDEBUG]\ax target=%s caster=%s spell=%s type=%s raw_mid=%s raw_last=%s",
                target.c_str(),
                caster.c_str(),
                spellName.c_str(),
                dmgKind,
                mid.c_str(),
                last.c_str()
            );
        }

        PostEvent("damage",
                  { {"attacker", caster},
                    {"target", target},
                    {"amount", amtBuf},
                    {"count", std::string("1")},
                    {"max", amtBuf},
                    {"type", std::string(dmgKind)},
                    {"spell", spellName} });
        return true;
    }

    // Form C: anonymous DoT tick. Match the spell against the recent-cast
    // cache to find a caster.
    std::string spell(mid_start);
    while (!spell.empty() && (spell.back() == '.' || spell.back() == ' '))
        spell.pop_back();
    std::string caster = LookupSpellCaster(spell);
    if (caster.empty()) return true; // unknown DoT, drop silently
    std::string owner = ResolveAttacker(caster);
    BumpDamage(owner, (uint32_t)amount);
    char amtBuf[32];
    std::snprintf(amtBuf, sizeof(amtBuf), "%llu", (unsigned long long)amount);
    PostEvent("damage",
              { {"attacker", caster},
                {"target", target},
                {"amount", amtBuf},
                {"count", std::string("1")},
                {"max", amtBuf},
                {"type", std::string("dot")},
                {"spell", spell} });
    return true;
}

// "<attacker> hit <target> for N points/point of non-melee damage."
bool ParseNonMelee(const char* line, const std::string& myName) {
    if (!FindSubstr(line, "non-melee damage")) return false;

    // Drop incoming.
    if (FindSubstr(line, " YOU ") || FindSubstr(line, " YOU.")
        || FindSubstr(line, " you ") || FindSubstr(line, " you.")) {
        return true;
    }

    const char* hitp = FindSubstr(line, " hit ");
    if (!hitp) return false;

    std::string attacker(line, hitp - line);
    Trim(attacker);
    if (attacker.empty()) return false;

    const char* tgt_start = hitp + 5;
    const char* forp = FindSubstr(tgt_start, " for ");
    if (!forp) return false;
    std::string target(tgt_start, forp - tgt_start);
    Trim(target);
    if (HP_IsInvalidFightTargetName(target)) return true;

    uint64_t amount = 0;
    if (!ParseUintWithCommas(forp + 5, &amount, nullptr)) return false;
    if (amount == 0) return false;

    bool wasCharmed = false;
    std::string owner = ResolveAttacker(attacker, &wasCharmed);
    bool ok = false;
    {
        std::lock_guard<std::mutex> lk(g_statsMutex);
        ok = g_knownChars.count(owner) > 0
             || IsKnownPet(attacker)
             || wasCharmed
             || LooksLikePcName(attacker);
    }
    if (!ok) return true; // drop mob-source nukes silently

    if (LooksLikePcName(attacker)) NoteKnownChar(attacker);

    BumpDamage(owner, (uint32_t)amount);
    char amtBuf[32];
    std::snprintf(amtBuf, sizeof(amtBuf), "%llu", (unsigned long long)amount);
    PostEvent("damage",
              { {"attacker", attacker},
                {"target", target},
                {"amount", amtBuf},
                {"count", std::string("1")},
                {"max", amtBuf},
                {"type", std::string("nonmelee")} });
    return true;
}

// "<attacker> <verb> <target> for N points/point of damage."  -- melee
// "You <verb> <target> for N points/point of damage."
bool ParseMelee(const char* line, const std::string& myName) {
    // Cheap reject.
    const char* pdmg = FindSubstr(line, "points of damage");
    if (!pdmg) pdmg = FindSubstr(line, "point of damage");
    if (!pdmg) return false;
    if (FindSubstr(line, "non-melee damage")) return false; // handled above
    if (FindSubstr(line, "healed")) return false;
    if (FindSubstr(line, "tries to ")) return false;
    if (FindSubstr(line, "but misses")) return false;

    // Do NOT drop Rampage/Flurry-style lines here. GamParse counts the real
    // outgoing damage, and skipping these was one reason HealTracker trailed
    // GamParse in raids.

    // Incoming mob->PC lines are handled by ParseIncomingMelee() for Tank/death
    // tracking. This outgoing DPS parser ignores direct YOU/you damage.
    if (FindSubstr(line, " YOU ") || FindSubstr(line, " YOU.")
        || FindSubstr(line, " you ") || FindSubstr(line, " you.")) {
        return true;
    }

    // Find " for <N> points/point of damage".
    const char* forp = nullptr;
    for (const char* q = pdmg; q > line + 4; --q) {
        if (q[0] == ' ' && q[1] == 'f' && q[2] == 'o' && q[3] == 'r' && q[4] == ' ') {
            forp = q; break;
        }
    }
    if (!forp) return false;

    uint64_t amount = 0;
    if (!ParseUintWithCommas(forp + 5, &amount, nullptr)) return false;
    if (amount == 0) return false;

    // left = "<attacker> <verb> <target>".
    // This restores the old optimized Lua behavior: split on the RIGHTMOST
    // known melee verb instead of assuming "first word = attacker". That keeps
    // multi-word targets/mobs intact and prevents dropped/shortened rows.
    std::string left(line, forp - line);
    Trim(left);
    if (left.empty()) return false;

    static const char* kMeleeVerbs[] = {
        // You-form / first-person verbs.
        " hit ", " slash ", " crush ", " pierce ", " bash ", " kick ",
        " claw ", " bite ", " gore ", " maul ", " sting ", " punch ",
        " strike ", " slice ", " smash ", " rend ", " slam ", " backstab ",
        " gnaw ", " slap ", " pummel ", " mangle ", " chomp ", " sweep ",
        " frenzy on ", " tail rake ", " burn ", " freeze ", " shoot ",

        // Third-person verbs.
        " hits ", " slashes ", " crushes ", " pierces ", " bashes ", " kicks ",
        " claws ", " bites ", " gores ", " mauls ", " stings ", " punches ",
        " strikes ", " slices ", " smashes ", " rends ", " slams ", " backstabs ",
        " gnaws ", " slaps ", " pummels ", " mangles ", " chomps ", " sweeps ",
        " frenzies on ", " tail rakes ", " burns ", " freezes ", " shoots ",
    };

    size_t bestPos = std::string::npos;
    size_t vlen = 0;
    for (const char* v : kMeleeVerbs) {
        const size_t vl = std::strlen(v);
        size_t from = 0;
        while (true) {
            size_t a = left.find(v, from);
            if (a == std::string::npos) break;
            if (bestPos == std::string::npos || a > bestPos) {
                bestPos = a;
                vlen = vl;
            }
            from = a + 1;
        }
    }
    if (bestPos == std::string::npos) return false;

    std::string attacker = left.substr(0, bestPos);
    std::string target   = left.substr(bestPos + vlen);
    Trim(attacker);
    Trim(target);

    if (attacker == "You" || attacker == "YOU" || attacker == "you")
        attacker = myName;

    if (attacker.empty() || target.empty()) return false;
    if (HP_IsInvalidFightTargetName(target)) return true;

    // Drop obvious mob->mob/player-target leakage from the DPS side. Real
    // incoming hits still go through ParseIncomingMelee().
    if (FindSubstr(target.c_str(), " hits ")
        || FindSubstr(target.c_str(), " slashes ")
        || FindSubstr(target.c_str(), " crushes ")
        || FindSubstr(target.c_str(), " bashes ")) {
        return true;
    }

    bool wasCharmed = false;
    std::string owner = ResolveAttacker(attacker, &wasCharmed);
    bool ok = false;
    {
        std::lock_guard<std::mutex> lk(g_statsMutex);
        ok = g_knownChars.count(owner) > 0
             || IsKnownPet(attacker)
             || wasCharmed
             || LooksLikePcName(attacker);
    }
    if (!ok) return true;

    if (LooksLikePcName(attacker)) NoteKnownChar(attacker);

    BumpDamage(owner, (uint32_t)amount);
    char amtBuf[32];
    std::snprintf(amtBuf, sizeof(amtBuf), "%llu", (unsigned long long)amount);
    PostEvent("damage",
              { {"attacker", attacker},
                {"target", target},
                {"amount", amtBuf},
                {"count", std::string("1")},
                {"max", amtBuf},
                {"type", std::string("melee")} });
    return true;
}

// ============================================================================
// INCOMING (mob -> player) + AVOIDANCE emitters.
//
// The outgoing parsers above intentionally DROP mob->player lines (they only
// feed the raid->mob DPS leaderboard). The Lua frontend needs the incoming
// side for the per-victim hit ring, Death Recap, and Tank-tab stats. Those
// were being re-parsed in Lua via broad mq.event matchers + mq.TLO.Spawn
// lookups on every combat line -- exactly the hot-path cost this plugin
// exists to remove. We emit them natively here instead.
//
// Victim classification is native and free: a target counts as a player only
// if it is "YOU"/myName or already in g_knownChars (which self-populates as
// raiders act). NO Spawn lookups. Mobs never enter g_knownChars, so boss
// names cannot leak in as phantom incoming events.
//
// New event kinds (bridge routes them; see heal_tracker_bridge.lua):
//   incoming|target=|attacker=|amount=|type=melee|nonmelee|dot[|spell=][|verb=]
//   avoid|target=|attacker=|kind=miss|parry|dodge|block|riposte
// ============================================================================

// Exact in-zone player lookup. This fixes incoming/tank damage for raiders
// who have not yet healed, cast, or dealt damage since plugin load.
// Older code only trusted g_knownChars, so a tank taking the first hits of
// a fight could be rejected as "not a player" until they appeared in another
// parser path.
bool IsPlayerSpawnByName(const std::string& name) {
    if (name.empty() || !pSpawnManager) return false;

    for (PlayerClient* cur = pSpawnManager->FirstSpawn; cur; cur = cur->GetNext()) {
        if (cur->Type != SPAWN_PLAYER) continue;

        const char* dn = cur->DisplayedName;
        const char* nm = cur->Name;
        if ((dn && dn[0] && name == dn) ||
            (nm && nm[0] && name == nm)) {
            return true;
        }
    }
    return false;
}


// Exact in-zone player-owned NPC lookup for tanking targets.
// This catches charmed/animated/summoned pets getting hit by mobs. Without this,
// incoming tank damage was only accepted when the victim was a player; pet
// victims like "Screamz`s Animated Corpse" or a charmed pet renamed "Hooker"
// were dropped or only partially counted by older Lua fallback listeners.
bool IsPlayerOwnedNpcByName(const std::string& name, std::string& ownerOut) {
    ownerOut.clear();
    if (name.empty() || !pSpawnManager) return false;

    for (PlayerClient* cur = pSpawnManager->FirstSpawn; cur; cur = cur->GetNext()) {
        if (cur->Type != SPAWN_NPC) continue;

        const char* dn = cur->DisplayedName;
        const char* nm = cur->Name;
        bool nameMatch =
            (dn && dn[0] && name == dn) ||
            (nm && nm[0] && name == nm);
        if (!nameMatch) continue;

        if (cur->MasterID != 0) {
            PlayerClient* master = GetSpawnByID(cur->MasterID);
            if (master && master->Type == SPAWN_PLAYER && master->Name[0]) {
                ownerOut.assign(master->Name);
                return true;
            }
        }
    }
    return false;
}

// Possessive pet target forms that appear directly in logs, e.g.
// "Screamz`s Animated Corpse", "Bob's pet", "Bob`s warder".
bool LooksLikePlayerPetTarget(const std::string& target, std::string& ownerOut) {
    ownerOut.clear();
    if (target.empty()) return false;

    size_t apos = std::string::npos;
    for (size_t i = 0; i + 2 < target.size(); ++i) {
        if ((target[i] == '`' || target[i] == '\'') && target[i + 1] == 's' && target[i + 2] == ' ') {
            apos = i;
            break;
        }
    }
    if (apos == std::string::npos) return false;

    std::string owner = target.substr(0, apos);
    std::string suffix = target.substr(apos + 3);
    Trim(owner); Trim(suffix);
    if (owner.empty() || suffix.empty()) return false;

    std::string lower = LowerCopy(suffix);
    bool petWord = lower.find("pet") != std::string::npos
                || lower.find("warder") != std::string::npos
                || lower.find("ward") != std::string::npos
                || lower.find("swarm") != std::string::npos
                || lower.find("corpse") != std::string::npos
                || lower.find("doppelganger") != std::string::npos
                || lower.find("illusion") != std::string::npos
                || lower.find("servant") != std::string::npos
                || lower.find("minion") != std::string::npos;
    if (!petWord) return false;

    {
        std::lock_guard<std::mutex> lk(g_statsMutex);
        if (g_knownChars.count(owner) || IsKnownPet(target)) {
            ownerOut = owner;
            return true;
        }
    }

    if (IsPlayerSpawnByName(owner)) {
        ownerOut = owner;
        NoteKnownChar(owner);
        return true;
    }
    return false;
}

// Returns true if `target` is one of our players. Normalizes YOU/you to
// myName via outName.
bool IncomingTargetIsPlayer(const std::string& target,
                            const std::string& myName,
                            std::string& outName) {
    if (target.empty()) return false;
    if (target == "YOU" || target == "you" || target == "Yourself"
        || target == "yourself" || target == myName) {
        outName = myName;
        return true;
    }

    {
        std::lock_guard<std::mutex> lk(g_statsMutex);
        if (g_knownChars.count(target)) { outName = target; return true; }
    }

    // Native spawn lookup catches raid/group members immediately, even before
    // they are learned through outgoing DPS, heals, or spell casts.
    if (IsPlayerSpawnByName(target)) {
        outName = target;
        NoteKnownChar(target);
        return true;
    }

    // Player-owned pet/charm targets should count in the Tank tab too. Keep
    // named pets separate from same-named players by appending the owner, just
    // like GamParse-style "Pet (Owner)" rows. Possessive pet names are already
    // unique enough, so keep their original display name.
    std::string petOwner;
    if (IsPlayerOwnedNpcByName(target, petOwner)) {
        if (!petOwner.empty()) NoteKnownChar(petOwner);
        if (!petOwner.empty() && target.find("`s ") == std::string::npos && target.find("'s ") == std::string::npos)
            outName = target + " (" + petOwner + ")";
        else
            outName = target;
        return true;
    }

    if (LooksLikePlayerPetTarget(target, petOwner)) {
        if (!petOwner.empty()) NoteKnownChar(petOwner);
        outName = target;
        return true;
    }

    return false;
}

// "<mob> <verb> <player> for N points/point of damage."
// Verb-anchored split so multi-word mob names ("a sand giant", "DPS Machine")
// stay intact. Mirrors the old Lua HT_MELEE_VERBS approach, in native code.
bool ParseIncomingMelee(const char* line, const std::string& myName) {
    const char* pdmg = FindSubstr(line, "points of damage");
    if (!pdmg) pdmg = FindSubstr(line, "point of damage");
    if (!pdmg) return false;
    if (FindSubstr(line, "non-melee damage")) return false;
    if (FindSubstr(line, "healed"))           return false;
    if (FindSubstr(line, "tries to "))        return false;
    if (FindSubstr(line, "but misses"))       return false;
    // Keep Rampage hits for incoming tank/death tracking.
    // These are real mob -> player/pet damage lines and were previously skipped.

    // Find the " for " that precedes the points-of-damage tail.
    const char* forp = nullptr;
    for (const char* q = pdmg; q > line + 4; --q) {
        if (q[0] == ' ' && q[1] == 'f' && q[2] == 'o' && q[3] == 'r' && q[4] == ' ') {
            forp = q; break;
        }
    }
    if (!forp) return false;

    uint64_t amount = 0;
    if (!ParseUintWithCommas(forp + 5, &amount, nullptr)) return false;
    if (amount == 0) return false;

    // left = "<attacker> <verb> <target>"
    std::string left(line, forp - line);
    Trim(left);
    if (left.empty()) return false;

    // Rightmost melee-verb occurrence splits attacker / verb / target.
    static const char* kMeleeVerbs[] = {
        " hits ", " slashes ", " crushes ", " pierces ", " bashes ", " kicks ",
        " claws ", " bites ", " gores ", " mauls ", " stings ", " punches ",
        " strikes ", " slices ", " smashes ", " rends ", " slams ", " backstabs ",
        " gnaws ", " slaps ", " pummels ", " mangles ", " chomps ", " sweeps ",
        " frenzies on ", " tail rakes ", " burns ", " freezes ",
    };
    size_t bestPos = std::string::npos, vlen = 0;
    for (const char* v : kMeleeVerbs) {
        size_t from = 0;
        size_t vl = std::strlen(v);
        while (true) {
            size_t a = left.find(v, from);
            if (a == std::string::npos) break;
            if (bestPos == std::string::npos || a > bestPos) { bestPos = a; vlen = vl; }
            from = a + 1;
        }
    }
    if (bestPos == std::string::npos) return false;

    std::string attacker = left.substr(0, bestPos);
    std::string verb     = left.substr(bestPos, vlen);
    std::string target   = left.substr(bestPos + vlen);
    Trim(attacker); Trim(verb); Trim(target);
    if (attacker.empty() || target.empty()) return false;

    std::string victim;
    if (!IncomingTargetIsPlayer(target, myName, victim)) return false;

    char amtBuf[32];
    std::snprintf(amtBuf, sizeof(amtBuf), "%llu", (unsigned long long)amount);
    PostEvent("incoming",
              { {"target", victim},
                {"attacker", attacker.empty() ? std::string("?") : attacker},
                {"amount", amtBuf},
                {"type", std::string("melee")},
                {"verb", verb.empty() ? std::string("melee") : verb} });
    return true;
}

// "<mob> hit <player> for N points/point of non-melee damage."
bool ParseIncomingNonMelee(const char* line, const std::string& myName) {
    if (!FindSubstr(line, "non-melee damage")) return false;
    const char* hitp = FindSubstr(line, " hit ");
    if (!hitp) return false;

    std::string attacker(line, hitp - line);
    Trim(attacker);

    const char* tgt_start = hitp + 5;
    const char* forp = FindSubstr(tgt_start, " for ");
    if (!forp) return false;
    std::string target(tgt_start, forp - tgt_start);
    Trim(target);

    std::string victim;
    if (!IncomingTargetIsPlayer(target, myName, victim)) return false;

    uint64_t amount = 0;
    if (!ParseUintWithCommas(forp + 5, &amount, nullptr)) return false;
    if (amount == 0) return false;

    char amtBuf[32];
    std::snprintf(amtBuf, sizeof(amtBuf), "%llu", (unsigned long long)amount);
    PostEvent("incoming",
              { {"target", victim},
                {"attacker", attacker.empty() ? std::string("?") : attacker},
                {"amount", amtBuf},
                {"type", std::string("nonmelee")} });
    return true;
}

// "<player> has taken N damage from <Spell> by <Caster>."  (DoT/spell tick)
// "<player> has taken N damage from <Spell>."
bool ParseIncomingDoT(const char* line, const std::string& myName) {
    const char* taken = FindSubstr(line, " has taken ");
    if (!taken) return false;

    std::string target(line, taken - line);
    Trim(target);
    std::string victim;
    if (!IncomingTargetIsPlayer(target, myName, victim)) return false;

    const char* p = taken + std::strlen(" has taken ");
    uint64_t amount = 0;
    const char* after = nullptr;
    if (!ParseUintWithCommas(p, &amount, &after)) return false;
    if (amount == 0) return false;
    if (!StartsWith(after, " damage from ")) return false;

    std::string rest(after + std::strlen(" damage from "));
    while (!rest.empty() && (rest.back() == '.' || rest.back() == ' ' || rest.back() == '!'))
        rest.pop_back();

    // Best-effort source/caster split. For incoming we mainly need a label.
    std::string spell = rest, caster;
    const char* byp = FindSubstr(rest.c_str(), " by ");
    if (byp) {
        spell.assign(rest.c_str(), byp - rest.c_str());
        caster.assign(byp + 4);
        Trim(spell); Trim(caster);
    } else if (StartsWith(rest.c_str(), "your ")) {
        spell = rest.substr(5);
    }

    char amtBuf[32];
    std::snprintf(amtBuf, sizeof(amtBuf), "%llu", (unsigned long long)amount);
    PostEvent("incoming",
              { {"target", victim},
                {"attacker", caster.empty() ? std::string("?") : caster},
                {"amount", amtBuf},
                {"type", std::string("dot")},
                {"spell", spell} });
    return true;
}

// Zero-damage avoidance lines. Long form carries attacker+victim+result:
//   "Mob tries to hit Tank, but misses!"  / "..., but Tank parries!"
// Short forms:
//   "Mob misses Tank."                 (attacker first)
//   "Tank parries Mob." / dodges / blocks / ripostes  (player first)
bool ParseAvoid(const char* line, const std::string& myName) {
    std::string attacker, target, resultWord;

    // Use a reliable local name for YOU lines. Some builds can call this before
    // myName was populated by the caller; if that happens the old code posted
    // target="" and the Lua side ignored the avoid event.
    std::string effectiveMyName = myName;
    if (effectiveMyName.empty()) {
        if (auto pChar = GetCharInfo()) {
            if (pChar->Name[0]) effectiveMyName = pChar->Name;
        }
    }

    const char* tries = FindSubstr(line, " tries to ");
    if (tries) {
        attacker.assign(line, tries - line);

        // Long form:
        //   "Ravenna Flameheart tries to crush YOU, but YOU riposte!"
        //   "Ravenna Flameheart tries to crush Dorfus, but Dorfus parries!"
        const char* afterVerb = tries + std::strlen(" tries to ");
        const char* verbEnd = std::strchr(afterVerb, ' ');
        if (!verbEnd) return false;
        const char* butp = FindSubstr(verbEnd, ", but ");
        if (!butp) return false;

        target.assign(verbEnd + 1, butp - (verbEnd + 1));
        resultWord.assign(butp + std::strlen(", but "));

        Trim(target);
        Trim(resultWord);

        // Result often includes the victim name first: "YOU riposte" or
        // "Dorfus parries". Strip that subject so kind detection is clean.
        std::string lw = LowerCopy(resultWord);
        std::string lt = LowerCopy(target);
        if (!lt.empty() && lw.rfind(lt + " ", 0) == 0) {
            resultWord.erase(0, target.size() + 1);
            Trim(resultWord);
        } else if (lw.rfind("you ", 0) == 0) {
            resultWord.erase(0, 4);
            Trim(resultWord);
        }

    } else if (FindSubstr(line, " misses ")) {
        const char* m = FindSubstr(line, " misses ");
        attacker.assign(line, m - line);
        target.assign(m + std::strlen(" misses "));
        resultWord = "misses";
    } else {
        // Player-subject short forms: "<player> <verb> <mob>."
        struct { const char* tok; const char* kind; } shorts[] = {
            { " parries ",  "parry"   },
            { " dodges ",   "dodge"   },
            { " blocks ",   "block"   },
            { " ripostes ", "riposte" },
            // Some clients/logs use singular first-person flavor.
            { " parry ",    "parry"   },
            { " dodge ",    "dodge"   },
            { " block ",    "block"   },
            { " riposte ",  "riposte" },
        };
        const char* hit = nullptr; const char* kind = nullptr; size_t toklen = 0;
        for (auto& s : shorts) {
            const char* h = FindSubstr(line, s.tok);
            if (h) { hit = h; kind = s.kind; toklen = std::strlen(s.tok); break; }
        }
        if (!hit) return false;
        target.assign(line, hit - line);          // player avoids
        attacker.assign(hit + toklen);            // mob
        resultWord = kind;
    }

    // Trim and strip trailing punctuation.
    Trim(attacker); Trim(target); Trim(resultWord);
    while (!target.empty() && (target.back() == '.' || target.back() == '!')) target.pop_back();
    while (!attacker.empty() && (attacker.back() == '.' || attacker.back() == '!')) attacker.pop_back();
    while (!resultWord.empty() && (resultWord.back() == '.' || resultWord.back() == '!')) resultWord.pop_back();
    Trim(target); Trim(attacker); Trim(resultWord);

    if (target == "YOU" || target == "You" || target == "you") {
        target = effectiveMyName;
    }

    std::string victim;
    if (!IncomingTargetIsPlayer(target, effectiveMyName, victim)) return false;

    // Classify the result keyword case-insensitively.
    std::string resultLower = LowerCopy(resultWord);
    const char* kind = nullptr;
    if      (resultLower.find("miss")   != std::string::npos) kind = "miss";
    else if (resultLower.find("parr")   != std::string::npos) kind = "parry";
    else if (resultLower.find("parry")  != std::string::npos) kind = "parry";
    else if (resultLower.find("dodg")   != std::string::npos) kind = "dodge";
    else if (resultLower.find("block")  != std::string::npos) kind = "block";
    else if (resultLower.find("ripost") != std::string::npos) kind = "riposte";
    if (!kind) return false;

    if (g_debug.load()) {
        WriteChatf("\ay[HP-AVOID]\ax target=%s attacker=%s kind=%s raw=%.100s",
            victim.c_str(), attacker.empty() ? "?" : attacker.c_str(), kind, line);
    }

    PostEvent("avoid",
              { {"target", victim},
                {"attacker", attacker.empty() ? std::string("?") : attacker},
                {"kind", std::string(kind)} });
    return true;
}


static std::string HP_FormatEqLogTimestampNow()
{
    std::time_t t = std::time(nullptr);
    std::tm tmv{};
#ifdef _WIN32
    localtime_s(&tmv, &t);
#else
    localtime_r(&t, &tmv);
#endif
    char buf[64] = { 0 };
    // Match EQ log timestamp style so the melee hit-log parser can recover
    // the real date/time even when the line came from OnIncomingChat instead
    // of the physical EQ log file.
    std::strftime(buf, sizeof(buf), "[%a %b %d %H:%M:%S %Y] ", &tmv);
    return std::string(buf);
}

static void HP_NoteFightLogLine(const char* line)
{
    if (!line || !*line) return;
    std::lock_guard<std::mutex> lk(g_liveDpsMutex);
    if (g_liveDps.mob.empty() || g_liveDps.total == 0) return;
    if (g_liveDps.logs.size() >= 2000)
        g_liveDps.logs.erase(g_liveDps.logs.begin(), g_liveDps.logs.begin() + (g_liveDps.logs.size() - 1999));

    // OnIncomingChat lines usually do not include the [Sun Jun 28 HH:MM:SS YYYY]
    // EQ-log prefix.  The Compare DPS melee-detail popup needs that timestamp,
    // so store a timestamped copy when the source line does not already have one.
    if (line[0] == '[')
        g_liveDps.logs.emplace_back(line);
    else
        g_liveDps.logs.emplace_back(HP_FormatEqLogTimestampNow() + line);
}

// Entry point. Returns true if the line was consumed.
bool ProcessLine(const char* raw, const std::string& myName) {
    if (!raw || !*raw) return false;

    // Strip "[timestamp] " prefix.
    const char* line = StripLogTimestamp(raw);
    if (g_auditEnabled.load()) g_auditCurrentRawLine = line;

    g_linesSeen.fetch_add(1, std::memory_order_relaxed);

    // Fast reject: every parser needs at least one of these keywords.
    bool hasPoints = FindSubstr(line, "points") != nullptr || FindSubstr(line, "point of damage") != nullptr || FindSubstr(line, "point of non-melee damage") != nullptr;
    bool hasTaken  = FindSubstr(line, " has taken ") != nullptr;
    bool hasHealed = FindSubstr(line, " healed ") != nullptr || FindSubstr(line, "healed by") != nullptr || FindSubstr(line, "healed for") != nullptr;
    bool hasCast   = FindSubstr(line, "begins to cast") != nullptr || StartsWith(line, "You begin casting ");
    bool hasSlain  = FindSubstr(line, "slain") != nullptr;
    bool hasRune   = FindSubstr(line, "shields you") != nullptr
                  || FindSubstr(line, "scales fade") != nullptr
                  || FindSubstr(line, "runes fades") != nullptr;
    // Zero-damage avoidance lines carry none of the keywords above.
    bool hasAvoid  = FindSubstr(line, " tries to ") != nullptr
                  || FindSubstr(line, " misses ")   != nullptr
                  || FindSubstr(line, " parries ")  != nullptr
                  || FindSubstr(line, " dodges ")   != nullptr
                  || FindSubstr(line, " blocks ")   != nullptr
                  || FindSubstr(line, " ripostes ") != nullptr
                  || FindSubstr(line, " parry")     != nullptr
                  || FindSubstr(line, " dodge")     != nullptr
                  || FindSubstr(line, " block")     != nullptr
                  || FindSubstr(line, " riposte")   != nullptr;

    if (!hasPoints && !hasTaken && !hasHealed && !hasCast && !hasSlain && !hasRune && !hasAvoid) {
        return false;
    }

    // Keep the fight-only raw line list for the Fight Summary -> View All Fight Logs popup.
    // Store the original raw line, not the timestamp-stripped text, so detail
    // popups can show the real EQ log time for each individual hit.
    HP_NoteFightLogLine(raw);

    // Order matters: cheaper rejects first, more specific patterns first.
    if (hasRune && ParseHealRune(line, myName)) { g_linesMatched.fetch_add(1); return true; }
    if (hasHealed) {
        if (ParseHealIn(line, myName))      { g_linesMatched.fetch_add(1); return true; }
        if (ParseHealInNoHas(line, myName)) { g_linesMatched.fetch_add(1); return true; }
        if (ParseHealSelfCast(line, myName)){ g_linesMatched.fetch_add(1); return true; }
        if (ParseHealOtherTarget(line, myName)) { g_linesMatched.fetch_add(1); return true; }
        if (ParseHealSelfProc(line, myName)){ g_linesMatched.fetch_add(1); return true; }
        if (ParseHealInAlt(line, myName))   { g_linesMatched.fetch_add(1); return true; }
    }
    if (hasCast && ParseSpellCast(line, myName)) { g_linesMatched.fetch_add(1); return true; }
    if (hasSlain && ParseKill(line, myName))     { g_linesMatched.fetch_add(1); return true; }
    if (hasTaken) {
        // Incoming DoT to a player is dropped by ParseSpellDamage; catch it first.
        if (ParseIncomingDoT(line, myName))  { g_linesMatched.fetch_add(1); return true; }
        if (ParseSpellDamage(line, myName))  { g_linesMatched.fetch_add(1); return true; }
    }
    if (hasPoints) {
        // Incoming (mob->player) is dropped by the outgoing parsers; catch it
        // first. These return false on outgoing lines and fall through.
        if (ParseIncomingNonMelee(line, myName)) { g_linesMatched.fetch_add(1); return true; }
        if (ParseIncomingMelee(line, myName))    { g_linesMatched.fetch_add(1); return true; }
        if (ParseNonMelee(line, myName)) { g_linesMatched.fetch_add(1); return true; }
        if (ParseMelee(line, myName))    { g_linesMatched.fetch_add(1); return true; }
    }
    if (hasAvoid && ParseAvoid(line, myName)) { g_linesMatched.fetch_add(1); return true; }

    if (g_auditEnabled.load() && (hasPoints || hasTaken)) {
        HP_AuditLine("UNMATCHED", std::string(), std::string(), std::string(line), 0, std::string(), std::string(), "combat-line-not-parsed");
    }
    return false;
}


static void HP_CommandImgTest()
{
    WriteChatf("\ag[HealParse]\ax ===== imgtest Demon.png =====");
#ifdef _WIN32
    ImGuiIO& io = ImGui::GetIO();
    WriteChatf("\ag[HealParse]\ax ImGui renderer: %s", io.BackendRendererName ? io.BackendRendererName : "(null)");
    WriteChatf("\ag[HealParse]\ax BackendRendererUserData: %s", io.BackendRendererUserData ? "YES" : "NO");
    WriteChatf("\ag[HealParse]\ax DX11 device available: %s", HP_GetImGuiDx11Device() ? "YES" : "NO");
    WriteChatf("\ag[HealParse]\ax DX9 device available: %s", HP_GetImGuiDx9Device() ? "YES" : "NO");

    auto paths = HP_GetDemonIconCandidatePaths();
    bool foundAny = false;
    for (const std::string& path : paths) {
        bool exists = HP_FileExistsA(path);
        WriteChatf("\ag[HealParse]\ax Looking for: %s", path.c_str());
        WriteChatf("\ag[HealParse]\ax File exists: %s", exists ? "YES" : "NO");
        if (!exists)
            continue;

        foundAny = true;
        std::vector<unsigned char> pixels;
        int decodeW = 0, decodeH = 0;
        bool decoded = HP_DecodePngBGRA(path, pixels, &decodeW, &decodeH);
        WriteChatf("\ag[HealParse]\ax PNG decode: %s  size=%dx%d", decoded ? "YES" : "NO", decodeW, decodeH);

        int w = 0, h = 0;
        ID3D11ShaderResourceView* srv = nullptr;
        bool dx11 = HP_LoadPngTextureDx11(path, &srv, &w, &h);
        WriteChatf("\ag[HealParse]\ax DX11 texture loaded: %s  size=%dx%d", dx11 ? "YES" : "NO", w, h);
        if (srv)
            srv->Release();

        w = h = 0;
        IDirect3DTexture9* tex9 = nullptr;
        bool dx9 = HP_LoadPngTextureDx9(path, &tex9, &w, &h);
        WriteChatf("\ag[HealParse]\ax DX9 texture loaded: %s  size=%dx%d", dx9 ? "YES" : "NO", w, h);
        if (tex9)
            tex9->Release();

        WriteChatf("\ag[HealParse]\ax Current cached texture: %s path=%s", g_demonIconTexture.id ? "YES" : "NO", g_demonIconTexture.loadedPath.empty() ? "(none)" : g_demonIconTexture.loadedPath.c_str());
        return;
    }

    if (!foundAny) {
        WriteChatf("\ar[HealParse]\ax Demon.png was not found in any checked path.");
        WriteChatf("\ay[HealParse]\ax Put it here: <MQ root>\\plugins\\MQ2HealParse\\Images\\Demon.png");
    }
#else
    WriteChatf("\ar[HealParse]\ax imgtest only supports Windows builds.");
#endif
}

// ----------------------------------------------------------------------------
// Slash command: /healparse [on|off|status|imgtest|reset|debug|pet link/add/del/list]
// ----------------------------------------------------------------------------

void Cmd_HealParse(SPAWNINFO* /*pChar*/, char* szLine) {
    char arg[MAX_STRING] = { 0 };
    GetArg(arg, szLine, 1);

    if (_stricmp(arg, "imgtest") == 0) { HP_CommandImgTest(); return; }
    if (_stricmp(arg, "commands") == 0 || _stricmp(arg, "help") == 0) {
        g_fullUiEnabled.store(true);
        g_fullUiTab.store(4);
        g_showCommandsWindow = true;
        WriteChatf("\ag[HealParse]\ax opened Commands window");
        return;
    }

    if (!arg[0] || _stricmp(arg, "status") == 0) {
        WriteChatf("\ag[HealParse]\ax enabled=%s push_to_lua=%s debug=%s audit=%s spell_dedup=%s",
            g_enabled.load() ? "on" : "off",
            g_pushToLua.load() ? "on" : "off",
            g_debug.load() ? "on" : "off",
            g_auditEnabled.load() ? "on" : "off",
            g_spellDamageDedupEnabled.load() ? "on" : "off");
        WriteChatf("\ag[HealParse]\ax lines_seen=%llu matched=%llu events_posted=%llu",
            (unsigned long long)g_linesSeen.load(),
            (unsigned long long)g_linesMatched.load(),
            (unsigned long long)g_eventsPosted.load());
        WriteChatf("\ag[HealParse]\ax source incoming=%llu writechat=%llu deduped=%llu queue=%zu",
            (unsigned long long)g_linesFromIncoming.load(),
            (unsigned long long)g_linesFromWriteChat.load(),
            (unsigned long long)g_linesDeduped.load(),
            g_eventQueue.size());
        std::lock_guard<std::mutex> lk(g_statsMutex);
        WriteChatf("\ag[HealParse]\ax known_chars=%zu pet_owners=%zu recent_casts=%zu",
            g_knownChars.size(), g_petOwners.size(), g_recentSpellCasts.size());
        WriteChatf("\ag[HealParse]\ax logtail=%s lines=%llu matched=%llu path=%s",
            g_logTailEnabled.load() ? "on" : "off",
            (unsigned long long)g_logTailLines.load(),
            (unsigned long long)g_logTailMatched.load(),
            g_logTailPath.empty() ? "(none)" : g_logTailPath.c_str());
        WriteChatf("\ag[HealParse]\ax liveui=%s alpha=%d force_visible=%s frames=%llu",
            g_liveOverlayEnabled.load() ? "on" : "off",
            g_liveOverlayAlphaPercent.load(),
            g_liveOverlayForceVisible.load() ? "yes" : "no",
            (unsigned long long)g_liveOverlayFrames.load());
        return;
    }
    if (_stricmp(arg, "on") == 0)  { g_enabled.store(true);  WriteChatf("\ag[HealParse]\ax parsing ENABLED"); return; }
    if (_stricmp(arg, "off") == 0) { g_enabled.store(false); WriteChatf("\ag[HealParse]\ax parsing DISABLED"); return; }
    if (_stricmp(arg, "pause") == 0) {
        // Alias for "push off". The heal_tracker Lua side calls this in its
        // /healtracker stop and /healtracker unload paths to silence the
        // plugin BEFORE Lua teardown begins. Once paused:
        //   - PostEvent is a no-op (the g_pushToLua check at its top bails).
        //   - The Drain TLO returns a static empty literal (see GetMember).
        // Together these guarantee no thread_local std::string pointers
        // are fed into MQ's chat formatter during the vsprintf_s_l danger
        // window. Silent on success -- callers use pcall(mq.cmd(...)) so
        // we don't spam chat with a "paused" message every /lua stop.
        g_pushToLua.store(false);
        return;
    }
    if (_stricmp(arg, "resume") == 0) {
        // Symmetric alias for "push on". Silent if we were already in the
        // resumed state -- HT_boot calls this on every /lua run as defense
        // against a sticky pause flag, and we don't want to spam chat on
        // every normal script reload. Only prints when actually flipping
        // the state, which is the case the user actually wants feedback for.
        bool was_paused = !g_pushToLua.exchange(true);
        if (was_paused) {
            WriteChatf("\ag[HealParse]\ax resumed (Lua push ENABLED)");
        }
        return;
    }
    if (_stricmp(arg, "push") == 0) {
        char arg2[MAX_STRING] = { 0 };
        GetArg(arg2, szLine, 2);
        if (_stricmp(arg2, "off") == 0) { g_pushToLua.store(false); WriteChatf("\ag[HealParse]\ax Lua push DISABLED"); }
        else { g_pushToLua.store(true);  WriteChatf("\ag[HealParse]\ax Lua push ENABLED"); }
        return;
    }
    if (_stricmp(arg, "debug") == 0) {
        char arg2[MAX_STRING] = { 0 };
        GetArg(arg2, szLine, 2);
        if (_stricmp(arg2, "off") == 0) { g_debug.store(false); WriteChatf("\ag[HealParse]\ax debug OFF"); }
        else { g_debug.store(true);  WriteChatf("\ag[HealParse]\ax debug ON"); }
        return;
    }
    if (_stricmp(arg, "audit") == 0) {
        char arg2[MAX_STRING] = { 0 };
        char arg3[MAX_STRING] = { 0 };
        GetArg(arg2, szLine, 2);
        GetArg(arg3, szLine, 3);
        if (_stricmp(arg2, "off") == 0) {
            g_auditEnabled.store(false);
            WriteChatf("\ag[HealParse]\ax audit OFF");
            return;
        }
        if (_stricmp(arg2, "clear") == 0) {
            std::lock_guard<std::mutex> lk(g_auditMutex);
            const std::string path = HP_GetAuditPath();
            std::ofstream out(path, std::ios::out | std::ios::trunc);
            out << "time\taction\tattacker\towner\ttarget\tamount\ttype\tspell\treason\tsource\traw_line\n";
            out.flush();
            WriteChatf("\ag[HealParse]\ax audit cleared: %s", path.c_str());
            return;
        }
        if (_stricmp(arg2, "path") == 0) {
            WriteChatf("\ag[HealParse]\ax audit path: %s", HP_GetAuditPath().c_str());
            return;
        }
        if (_stricmp(arg2, "player") == 0) {
            g_auditPlayerFilter = arg3;
            if (_stricmp(g_auditPlayerFilter.c_str(), "all") == 0) g_auditPlayerFilter.clear();
            WriteChatf("\ag[HealParse]\ax audit player filter: %s", g_auditPlayerFilter.empty() ? "ALL" : g_auditPlayerFilter.c_str());
            return;
        }
        // default: on
        std::string path;
        {
            std::lock_guard<std::mutex> lk(g_auditMutex);
            path = HP_GetAuditPath();
            std::ofstream out(path, std::ios::out | std::ios::app);
            if (!out.good()) {
                WriteChatf("\ar[HealParse]\ax audit could not write: %s", path.c_str());
                return;
            }
            HP_EnsureAuditHeaderUnlocked(out, path);
            out.flush();
        }
        g_auditEnabled.store(true);
        WriteChatf("\ag[HealParse]\ax audit ON -> %s", path.c_str());
        return;
    }
    if (_stricmp(arg, "dedup") == 0) {
        char arg2[MAX_STRING] = { 0 };
        char arg3[MAX_STRING] = { 0 };
        GetArg(arg2, szLine, 2);
        GetArg(arg3, szLine, 3);
        if (_stricmp(arg2, "spell") == 0) {
            if (_stricmp(arg3, "on") == 0) g_spellDamageDedupEnabled.store(true);
            else g_spellDamageDedupEnabled.store(false);
            WriteChatf("\ag[HealParse]\ax spell damage de-dupe %s", g_spellDamageDedupEnabled.load() ? "ON" : "OFF");
            return;
        }
        WriteChatf("\ag[HealParse]\ax usage: /healparse dedup spell on|off");
        return;
    }
    if (_stricmp(arg, "logpath") == 0) {
        const char* rest = szLine ? szLine : "";
        while (*rest == ' ' || *rest == '\t') ++rest;
        while (*rest && *rest != ' ' && *rest != '\t') ++rest; // skip logpath
        while (*rest == ' ' || *rest == '\t') ++rest;
        g_logTailPath = rest;
        if (g_logTailPath.size() >= 2 &&
            ((g_logTailPath.front() == '"' && g_logTailPath.back() == '"') ||
             (g_logTailPath.front() == '\'' && g_logTailPath.back() == '\''))) {
            g_logTailPath = g_logTailPath.substr(1, g_logTailPath.size() - 2);
        }
        CloseLogTailer();
        WriteChatf("\ag[HealParse]\ax logpath set: %s", g_logTailPath.c_str());
        return;
    }
    if (_stricmp(arg, "logtail") == 0) {
        char arg2[MAX_STRING] = { 0 };
        GetArg(arg2, szLine, 2);
        if (_stricmp(arg2, "off") == 0) {
            g_logTailEnabled.store(false);
            CloseLogTailer();
        } else {
            g_logTailEnabled.store(true);
            OpenLogTailerIfNeeded();
        }
        WriteChatf("\ag[HealParse]\ax C++ logtail %s", g_logTailEnabled.load() ? "on" : "off");
        return;
    }
    if (_stricmp(arg, "liveui") == 0 || _stricmp(arg, "overlay") == 0) {
        char arg2[MAX_STRING] = { 0 };
        char arg3[MAX_STRING] = { 0 };
        GetArg(arg2, szLine, 2);
        GetArg(arg3, szLine, 3);
        if (_stricmp(arg2, "off") == 0) {
            g_liveOverlayEnabled.store(false);
            WriteChatf("\ag[HealParse]\ax plugin live DPS overlay OFF");
            return;
        }
        if (_stricmp(arg2, "reset") == 0 || _stricmp(arg2, "resetpos") == 0 || _stricmp(arg2, "show") == 0) {
            g_liveOverlayEnabled.store(true);
            g_liveOverlayForceVisible.store(true);
            g_liveOverlayResetPos.store(true);
            WriteChatf("\ag[HealParse]\ax plugin live DPS overlay ON - position reset");
            return;
        }
        if (_stricmp(arg2, "auto") == 0) {
            g_liveOverlayEnabled.store(true);
            g_liveOverlayForceVisible.store(false);
            WriteChatf("\ag[HealParse]\ax plugin live DPS overlay AUTO (combat only)");
            return;
        }
        if (_stricmp(arg2, "alpha") == 0) {
            int v = atoi(arg3);
            if (v < 10) v = 10;
            if (v > 100) v = 100;
            g_liveOverlayAlphaPercent.store(v);
            WriteChatf("\ag[HealParse]\ax plugin live DPS overlay alpha=%d", v);
            return;
        }
        g_liveOverlayEnabled.store(true);
        g_liveOverlayForceVisible.store(true);
        WriteChatf("\ag[HealParse]\ax plugin live DPS overlay ON");
        return;
    }
    if (_stricmp(arg, "ui") == 0 || _stricmp(arg, "fullui") == 0) {
        char arg2[MAX_STRING] = { 0 };
        GetArg(arg2, szLine, 2);
        if (_stricmp(arg2, "off") == 0) {
            g_fullUiEnabled.store(false);
            WriteChatf("\ag[HealParse]\ax full plugin UI OFF");
            return;
        }
        if (_stricmp(arg2, "reset") == 0 || _stricmp(arg2, "resetpos") == 0) {
            g_fullUiEnabled.store(true);
            g_fullUiResetPos.store(true);
            WriteChatf("\ag[HealParse]\ax full plugin UI ON - position reset");
            return;
        }
        g_fullUiEnabled.store(true);
        WriteChatf("\ag[HealParse]\ax full plugin UI ON");
        return;
    }
    if (_stricmp(arg, "view") == 0) {
        char a2[MAX_STRING] = { 0 };
        GetArg(a2, szLine, 2);
        if      (_stricmp(a2, "dps") == 0)                              g_liveOverlayView.store(0);
        else if (_stricmp(a2, "heals") == 0)                           g_liveOverlayView.store(1);
        else if (_stricmp(a2, "burns") == 0 || _stricmp(a2, "timers") == 0) g_liveOverlayView.store(2);
        else                                                           g_liveOverlayView.store((g_liveOverlayView.load() + 1) % 3);
        g_liveOverlayEnabled.store(true);
        const char* nm[3] = { "DPS", "Heals", "Burns" };
        WriteChatf("\ag[HealParse]\ax overlay view: %s", nm[g_liveOverlayView.load() % 3]);
        return;
    }
    if (_stricmp(arg, "burn") == 0) {
        // Push/refresh a burn timer from Lua disc/AA listeners:
        //   /healparse burn <who>|<label>|<seconds>
        //   /healparse burn clear
        const char* rest = szLine ? szLine : "";
        while (*rest == ' ' || *rest == '\t') ++rest;
        while (*rest && *rest != ' ' && *rest != '\t') ++rest; // skip "burn"
        while (*rest == ' ' || *rest == '\t') ++rest;
        std::string s(rest);
        if (_strnicmp(s.c_str(), "clear", 5) == 0) {
            std::lock_guard<std::mutex> lk(g_liveBurnsMutex);
            g_liveBurns.clear();
            WriteChatf("\ag[HealParse]\ax burns cleared");
            return;
        }
        size_t p1 = s.find('|');
        size_t p2 = (p1 == std::string::npos) ? std::string::npos : s.find('|', p1 + 1);
        if (p1 == std::string::npos || p2 == std::string::npos) {
            WriteChatf("\ay[HealParse]\ax usage: /healparse burn <who>|<label>|<seconds>");
            return;
        }
        std::string who = s.substr(0, p1);
        std::string label = s.substr(p1 + 1, p2 - p1 - 1);
        int secs = atoi(s.c_str() + p2 + 1);
        auto trim = [](std::string& x) {
            size_t a = x.find_first_not_of(" \t");
            if (a == std::string::npos) { x.clear(); return; }
            size_t b = x.find_last_not_of(" \t");
            x = x.substr(a, b - a + 1);
        };
        trim(who); trim(label);
        AddLiveBurn(who, label, secs);
        return;
    }
    if (_stricmp(arg, "burnrule") == 0 || _stricmp(arg, "burntimer") == 0) {
        char op[MAX_STRING] = { 0 };
        GetArg(op, szLine, 2);
        if (_stricmp(op, "list") == 0) {
            auto rules = HP_GetBurnTriggerRulesForUi();
            WriteChatf("\ag[HealParse]\ax Burn timer triggers: %zu", rules.size());
            for (const auto& r : rules) {
                WriteChatf("\at%s\ax -> \ay%s\ax (%ds) %s", r.trigger.c_str(), (r.display.empty() ? r.trigger.c_str() : r.display.c_str()), r.seconds, r.enabled ? "" : "OFF");
            }
            return;
        }
        if (_stricmp(op, "clear") == 0) {
            std::lock_guard<std::mutex> lk(g_burnTriggerRulesMutex);
            g_burnTriggerRules.clear();
            HP_SaveBurnTriggersUnlocked();
            WriteChatf("\ag[HealParse]\ax burn timer triggers cleared");
            return;
        }
        if (_stricmp(op, "add") == 0 || _stricmp(op, "set") == 0) {
            const char* rest = szLine ? szLine : "";
            while (*rest == ' ' || *rest == '\t') ++rest;
            while (*rest && *rest != ' ' && *rest != '\t') ++rest; // burnrule
            while (*rest == ' ' || *rest == '\t') ++rest;
            while (*rest && *rest != ' ' && *rest != '\t') ++rest; // add
            while (*rest == ' ' || *rest == '\t') ++rest;
            std::string payload(rest);
            size_t p1 = payload.find('|');
            size_t p2 = (p1 == std::string::npos) ? std::string::npos : payload.find('|', p1 + 1);
            if (p1 == std::string::npos || p2 == std::string::npos) {
                WriteChatf("\ay[HealParse]\ax usage: /healparse burnrule add <trigger>|<display>|<seconds>");
                return;
            }
            std::string trigger = payload.substr(0, p1);
            std::string display = payload.substr(p1 + 1, p2 - p1 - 1);
            int secs = atoi(payload.c_str() + p2 + 1);
            HP_SetBurnTriggerRule(trigger, display, secs, true);
            WriteChatf("\ag[HealParse]\ax burn trigger saved: %s -> %s (%ds)", HP_TrimCopy(trigger).c_str(), HP_TrimCopy(display).empty() ? HP_TrimCopy(trigger).c_str() : HP_TrimCopy(display).c_str(), std::max(1, secs));
            return;
        }
        g_showBurnTimersWindow = true;
        g_fullUiEnabled.store(true);
        g_fullUiTab.store(4);
        WriteChatf("\ag[HealParse]\ax opened Burn Timers window");
        return;
    }
    if (_stricmp(arg, "reset") == 0) {
        std::lock_guard<std::mutex> lk(g_statsMutex);
        g_healByTarget.clear();
        g_damageByAttacker.clear();
        g_spellCastsByCaster.clear();
        g_spellCastsBySpell.clear();
        g_recentSpellCasts.clear();
        {
            std::lock_guard<std::mutex> lk2(g_liveDpsMutex);
            g_liveDps = LiveDpsFight{};
        }
        {
            std::lock_guard<std::mutex> lk3(g_liveHealsMutex);
            g_liveHeals = LiveHealFight{};
        }
        {
            std::lock_guard<std::mutex> lk4(g_liveTankMutex);
            g_liveTank.clear();
        }
        // Keep g_knownChars and g_petOwners.
        g_linesSeen.store(0);
        g_linesMatched.store(0);
        g_eventsPosted.store(0);
        WriteChatf("\ag[HealParse]\ax stats reset");
        return;
    }
    if (_stricmp(arg, "pet") == 0) {
        char op[MAX_STRING] = { 0 };
        GetArg(op, szLine, 2);

        // Persistent manual pet-owner links.  These links are used by
        // AttributeDamage()/ResolveAttacker(), so pet damage is credited to
        // the owner everywhere in the live DPS and Player Damage sections.
        //
        // Supported:
        //   /healparse pet link <owner> <pet name...>
        //   /healparse pet add <pet> <owner>          (old single-word format)
        //   /healparse pet del <pet name...>
        //   /healparse pet list
        //   /healparse pet clear
        //   /healparse pet save
        //   /healparse pet load
        if (_stricmp(op, "link") == 0 || _stricmp(op, "owner") == 0 || _stricmp(op, "set") == 0) {
            char ownerName[MAX_STRING] = { 0 };
            GetArg(ownerName, szLine, 3);

            const char* rest = szLine ? szLine : "";
            // skip: pet/op, link, owner
            for (int i = 0; i < 3 && *rest; ++i) {
                while (*rest == ' ' || *rest == '\t') ++rest;
                while (*rest && *rest != ' ' && *rest != '\t') ++rest;
            }
            while (*rest == ' ' || *rest == '\t') ++rest;
            HP_SetPetOwner(rest, ownerName, true);
            return;
        }
        if (_stricmp(op, "add") == 0) {
            char petName[MAX_STRING] = { 0 };
            char ownerName[MAX_STRING] = { 0 };
            GetArg(petName, szLine, 3);
            GetArg(ownerName, szLine, 4);
            HP_SetPetOwner(petName, ownerName, true);
            return;
        }
        if (_stricmp(op, "del") == 0 || _stricmp(op, "remove") == 0 || _stricmp(op, "unlink") == 0) {
            const char* rest = szLine ? szLine : "";
            // skip: pet/op, del
            for (int i = 0; i < 2 && *rest; ++i) {
                while (*rest == ' ' || *rest == '\t') ++rest;
                while (*rest && *rest != ' ' && *rest != '\t') ++rest;
            }
            while (*rest == ' ' || *rest == '\t') ++rest;
            std::string pet = HP_TrimCopy(rest);
            if (pet.empty()) {
                WriteChatf("\ar[HealParse]\ax usage: /healparse pet del <pet name>");
                return;
            }
            std::lock_guard<std::mutex> lk(g_statsMutex);
            g_petOwners.erase(pet);
            HP_SavePetOwnersUnlocked();
            WriteChatf("\ag[HealParse]\ax pet link removed: %s", pet.c_str());
            return;
        }
        if (_stricmp(op, "list") == 0) {
            std::lock_guard<std::mutex> lk(g_statsMutex);
            WriteChatf("\ag[HealParse]\ax pet links: %zu", g_petOwners.size());
            for (auto& kv : g_petOwners) {
                WriteChatf("  %s -> %s", kv.first.c_str(), kv.second.c_str());
            }
            return;
        }
        if (_stricmp(op, "clear") == 0) {
            std::lock_guard<std::mutex> lk(g_statsMutex);
            g_petOwners.clear();
            HP_SavePetOwnersUnlocked();
            WriteChatf("\ag[HealParse]\ax all pet links cleared");
            return;
        }
        if (_stricmp(op, "save") == 0) {
            std::lock_guard<std::mutex> lk(g_statsMutex);
            HP_SavePetOwnersUnlocked();
            WriteChatf("\ag[HealParse]\ax pet links saved: %s", kPetOwnersFileName);
            return;
        }
        if (_stricmp(op, "load") == 0 || _stricmp(op, "reload") == 0) {
            HP_LoadPetOwners();
            WriteChatf("\ag[HealParse]\ax pet links loaded: %s", kPetOwnersFileName);
            return;
        }

        WriteChatf("\ag[HealParse]\ax usage: /healparse pet link <owner> <pet name...> | add <pet> <owner> | del <pet> | list | clear");
        return;
    }
    if (_stricmp(arg, "minheal") == 0) {
        char arg2[MAX_STRING] = { 0 };
        GetArg(arg2, szLine, 2);
        int v = atoi(arg2);
        if (v >= 0) { g_minHealAmount.store(v); WriteChatf("\ag[HealParse]\ax minHealAmount=%d", v); }
        return;
    }
    if (_stricmp(arg, "charm") == 0) {
        char op[MAX_STRING] = { 0 };
        GetArg(op, szLine, 2);
        if (_stricmp(op, "test") == 0) {
            // /healparse charm test <name...>
            // GetArg returns one token; rebuild from arg 3 to end for
            // multi-word mob names. Easiest is just GetArg with the rest
            // flag, but we'll do it manually for clarity.
            const char* rest = szLine;
            // Skip "charm test " prefix.
            int skipped = 0;
            while (*rest && skipped < 2) {
                if (*rest == ' ') ++skipped;
                ++rest;
            }
            while (*rest == ' ') ++rest;
            if (!*rest) {
                WriteChatf("\ag[HealParse]\ax usage: /healparse charm test <mob name>");
                return;
            }
            std::string name(rest);
            // Trim trailing whitespace.
            while (!name.empty() && (name.back() == ' ' || name.back() == '\t'))
                name.pop_back();

            std::string owner = LookupCharmedPetOwner(name);
            bool onlyCharmed = HasOnlyCharmedSpawn(name);
            WriteChatf("\ag[HealParse]\ax charm test '%s': owner='%s' onlyCharmed=%s",
                       name.c_str(),
                       owner.empty() ? "<none>" : owner.c_str(),
                       onlyCharmed ? "true" : "false");
            return;
        }
        if (_stricmp(op, "cache") == 0) {
            std::lock_guard<std::mutex> lk(g_petOwnerCacheMutex);
            WriteChatf("\ag[HealParse]\ax charm cache: %zu entries", g_petOwnerCache.size());
            int64_t now = NowMs();
            for (auto& kv : g_petOwnerCache) {
                WriteChatf("  '%s' -> '%s' (%lld ms left)",
                           kv.first.c_str(),
                           kv.second.owner.empty() ? "<not a pet>" : kv.second.owner.c_str(),
                           (long long)(kv.second.expiryMs - now));
            }
            return;
        }
        if (_stricmp(op, "clear") == 0) {
            ClearPetOwnerCache();
            WriteChatf("\ag[HealParse]\ax charm cache cleared");
            return;
        }
        WriteChatf("\ag[HealParse]\ax usage: /healparse charm [test <mob>|cache|clear]");
        return;
    }

    WriteChatf("\ag[HealParse]\ax usage: /healparse [on|off|status|commands|debug on|off|audit on|off|audit player <name>|dedup spell on|off|push on|off|pause|resume|pet link <owner> <pet>|minheal <N>|charm test <mob>]");
}

// ----------------------------------------------------------------------------
// TLO: ${HealParse.X}
// ----------------------------------------------------------------------------

class MQ2HealParseType : public MQ2Type {
public:
    enum class Members {
        Enabled,
        LinesSeen,
        LinesMatched,
        EventsPosted,
        KnownChars,
        TotalDamage,
        TotalHeals,
        DamageBy,        // ${HealParse.DamageBy[Name]}
        HealsOn,         // ${HealParse.HealsOn[Name]}
        SpellCasts,      // ${HealParse.SpellCasts[Name]}
        CharmedOwner,    // ${HealParse.CharmedOwner[Mob]} -> owner or empty
        OnlyCharmedSpawn,// ${HealParse.OnlyCharmedSpawn[Mob]} -> bool
        Drain,           // ${HealParse.Drain[N]} -> up to N queued events joined by \n
        QueueDepth,      // ${HealParse.QueueDepth} -> current queue size
        LiveDPS,         // ${HealParse.LiveDPS} -> compact plugin-owned live DPS snapshot
    };

    MQ2HealParseType() : MQ2Type("HealParse") {
        ScopedTypeMember(Members, Enabled);
        ScopedTypeMember(Members, LinesSeen);
        ScopedTypeMember(Members, LinesMatched);
        ScopedTypeMember(Members, EventsPosted);
        ScopedTypeMember(Members, KnownChars);
        ScopedTypeMember(Members, TotalDamage);
        ScopedTypeMember(Members, TotalHeals);
        ScopedTypeMember(Members, DamageBy);
        ScopedTypeMember(Members, HealsOn);
        ScopedTypeMember(Members, SpellCasts);
        ScopedTypeMember(Members, CharmedOwner);
        ScopedTypeMember(Members, OnlyCharmedSpawn);
        ScopedTypeMember(Members, Drain);
        ScopedTypeMember(Members, QueueDepth);
        ScopedTypeMember(Members, LiveDPS);
    }

    bool GetMember(MQVarPtr VarPtr, const char* Member, char* Index, MQTypeVar& Dest) override {
        auto pMember = MQ2HealParseType::FindMember(Member);
        if (!pMember) return false;

        switch (static_cast<Members>(pMember->ID)) {
        case Members::Enabled:
            Dest.Set(g_enabled.load());
            Dest.Type = mq::datatypes::pBoolType;
            return true;
        case Members::LinesSeen:
            Dest.Set((int64_t)g_linesSeen.load());
            Dest.Type = mq::datatypes::pInt64Type;
            return true;
        case Members::LinesMatched:
            Dest.Set((int64_t)g_linesMatched.load());
            Dest.Type = mq::datatypes::pInt64Type;
            return true;
        case Members::EventsPosted:
            Dest.Set((int64_t)g_eventsPosted.load());
            Dest.Type = mq::datatypes::pInt64Type;
            return true;
        case Members::KnownChars: {
            std::lock_guard<std::mutex> lk(g_statsMutex);
            Dest.Set((int)g_knownChars.size());
            Dest.Type = mq::datatypes::pIntType;
            return true;
        }
        case Members::TotalDamage: {
            std::lock_guard<std::mutex> lk(g_statsMutex);
            uint64_t total = 0;
            for (auto& kv : g_damageByAttacker) total += kv.second.total;
            Dest.Set((int64_t)total);
            Dest.Type = mq::datatypes::pInt64Type;
            return true;
        }
        case Members::TotalHeals: {
            std::lock_guard<std::mutex> lk(g_statsMutex);
            uint64_t total = 0;
            for (auto& kv : g_healByTarget) total += kv.second.total;
            Dest.Set((int64_t)total);
            Dest.Type = mq::datatypes::pInt64Type;
            return true;
        }
        case Members::DamageBy: {
            if (!Index || !*Index) return false;
            std::lock_guard<std::mutex> lk(g_statsMutex);
            auto it = g_damageByAttacker.find(Index);
            uint64_t v = (it == g_damageByAttacker.end()) ? 0 : it->second.total;
            Dest.Set((int64_t)v);
            Dest.Type = mq::datatypes::pInt64Type;
            return true;
        }
        case Members::HealsOn: {
            if (!Index || !*Index) return false;
            std::lock_guard<std::mutex> lk(g_statsMutex);
            auto it = g_healByTarget.find(Index);
            uint64_t v = (it == g_healByTarget.end()) ? 0 : it->second.total;
            Dest.Set((int64_t)v);
            Dest.Type = mq::datatypes::pInt64Type;
            return true;
        }
        case Members::SpellCasts: {
            if (!Index || !*Index) return false;
            std::lock_guard<std::mutex> lk(g_statsMutex);
            auto it = g_spellCastsByCaster.find(Index);
            uint32_t v = (it == g_spellCastsByCaster.end()) ? 0 : it->second;
            Dest.Set((int)v);
            Dest.Type = mq::datatypes::pIntType;
            return true;
        }
        case Members::CharmedOwner: {
            // ${HealParse.CharmedOwner[<mob name>]} -> owner string, or
            // empty string when the mob isn't a player-owned pet.
            // Buffer must outlive this call; use a thread_local static.
            static thread_local char buf[MAX_STRING];
            buf[0] = '\0';
            if (Index && *Index) {
                std::string owner = LookupCharmedPetOwner(Index);
                if (!owner.empty()) {
                    std::strncpy(buf, owner.c_str(), sizeof(buf) - 1);
                    buf[sizeof(buf) - 1] = '\0';
                }
            }
            Dest.Ptr = &buf[0];
            Dest.Type = mq::datatypes::pStringType;
            return true;
        }
        case Members::OnlyCharmedSpawn: {
            // ${HealParse.OnlyCharmedSpawn[<mob name>]} -> bool. True only
            // when every same-named spawn is a charmed pet.
            bool v = false;
            if (Index && *Index) v = HasOnlyCharmedSpawn(Index);
            Dest.Set(v);
            Dest.Type = mq::datatypes::pBoolType;
            return true;
        }
        case Members::LiveDPS: {
            static thread_local std::string liveBuf;
            liveBuf = BuildLiveDpsSnapshot();
            Dest.Ptr = const_cast<char*>(liveBuf.c_str());
            Dest.Type = mq::datatypes::pStringType;
            return true;
        }
        case Members::Drain: {
            // ${HealParse.Drain[N]} -> string. Pops up to N events from
            // the queue and returns them joined by '\n'. Each event is
            // "kind|k=v|k=v|...". The bridge parses and dispatches.
            //
            // Index may be empty / "0" / a number. We cap defensively.
            //
            // CRASH-HARDENING (the vsprintf_s_l-on-/lua-stop fix):
            // ----------------------------------------------------
            // On MQ 3.1.4.x, mq2lua.DLL can crash in vsprintf_s_l / wscanf_s /
            // snprintf when a Lua script with ImGui callbacks is torn down by
            // /lua stop. The crash window is the brief period between the
            // moment Lua starts unwinding and the moment all our C-side
            // callbacks (mq.event, mq.bind, ImGui frames, actor IPC) actually
            // stop firing. During that window, anything that hands a non-
            // static string pointer back through MQ's formatter is unsafe --
            // including the thread_local std::string buffer this TLO used to
            // return unconditionally.
            //
            // The Lua side now calls "/healparse pause" at the very top of
            // its /healtracker stop and /healtracker unload paths. That sets
            // g_pushToLua = false. From that point on we:
            //   1) Skip touching g_eventQueue entirely (no mutex, no allocs,
            //      no thread_local writes).
            //   2) Return a true static-storage const char* ("") so MQ's
            //      formatter has a stable, unmoving pointer to read from.
            //
            // The static literal is in .rodata; it lives for the lifetime
            // of the DLL. Even if mq2lua re-reads the pointer microseconds
            // after the TLO returns (which is what the crash trace suggests
            // it does), the bytes at that address are still "\0". No
            // formatter on earth crashes on an empty string.
            static const char* kEmpty = "";
            if (!g_pushToLua.load()) {
                Dest.Ptr = (void*)kEmpty;
                Dest.Type = mq::datatypes::pStringType;
                return true;
            }

            static thread_local std::string buf;
            size_t n = 256;
            if (Index && *Index) {
                long parsed = std::atol(Index);
                if (parsed > 0) n = (size_t)parsed;
            }
            if (n > 262144) n = 262144; // allow full raid-burst drains; Lua bridge requests up to 262144

            // Defensive try/catch: DrainEventQueue acquires a mutex and does
            // string allocations. If anything throws (out-of-memory, weird
            // STL state during DLL teardown), we fall back to the static
            // empty literal rather than letting the exception escape into
            // MQ's TLO dispatch which has no idea what to do with it.
            try {
                buf = DrainEventQueue(n);
            } catch (...) {
                buf.clear();
            }

            // Belt-and-suspenders: if buf is empty, return the static
            // literal rather than buf.c_str(). std::string's c_str() on an
            // empty string is *usually* a pointer to the small-string
            // buffer inside the std::string object, which lives in
            // thread_local storage -- safe in steady state, but during DLL
            // teardown thread_local destructors run and that pointer goes
            // bad. The static literal is always safe.
            Dest.Ptr = buf.empty() ? (void*)kEmpty : (void*)buf.c_str();
            Dest.Type = mq::datatypes::pStringType;
            return true;
        }
        case Members::QueueDepth: {
            std::lock_guard<std::mutex> lk(g_eventQueueMutex);
            Dest.Set((int)g_eventQueue.size());
            Dest.Type = mq::datatypes::pIntType;
            return true;
        }
        }
        return false;
    }

    bool ToString(MQVarPtr /*VarPtr*/, char* Destination) override {
        strcpy_s(Destination, MAX_STRING, g_enabled.load() ? "TRUE" : "FALSE");
        return true;
    }
};

MQ2HealParseType* pHealParseType = nullptr;

bool dataHealParse(const char* /*szIndex*/, MQTypeVar& Ret) {
    Ret.DWord = 1;
    Ret.Type = pHealParseType;
    return true;
}

// ----------------------------------------------------------------------------
// C++ EQ log tailer. GamParse reads the final EQ log; this tailer reads the same
// file inside MQ2HealParse so Lua does not have to parse the log. When enabled
// with /healparse logpath <path> + /healparse logtail on, chat callbacks are
// used only as a fallback until the log path is ready, preventing double-counts.
// ----------------------------------------------------------------------------
void CloseLogTailer()
{
    if (g_logTailFile) {
        std::fclose(g_logTailFile);
        g_logTailFile = nullptr;
    }
    g_logTailOffset = 0;
    g_logTailInitialized = false;
}

bool OpenLogTailerIfNeeded()
{
    if (!g_logTailEnabled.load()) return false;
    if (g_logTailPath.empty()) return false;
    if (g_logTailFile) return true;

    g_logTailFile = std::fopen(g_logTailPath.c_str(), "rb");
    if (!g_logTailFile) return false;

    // Start at EOF so loading/reloading the plugin does not replay old fights.
    std::fseek(g_logTailFile, 0, SEEK_END);
    long pos = std::ftell(g_logTailFile);
    g_logTailOffset = (pos > 0) ? static_cast<uint64_t>(pos) : 0;
    g_logTailInitialized = true;
    return true;
}

void TailPluginLog()
{
    if (!g_enabled.load()) return;
    if (!g_logTailEnabled.load()) return;
    if (!OpenLogTailerIfNeeded()) return;

    // Rotation/shrink check.
    std::fseek(g_logTailFile, 0, SEEK_END);
    long endPos = std::ftell(g_logTailFile);
    if (endPos < 0) return;
    if (static_cast<uint64_t>(endPos) < g_logTailOffset) {
        CloseLogTailer();
        OpenLogTailerIfNeeded();
        return;
    }
    if (static_cast<uint64_t>(endPos) == g_logTailOffset) return;

    std::fseek(g_logTailFile, static_cast<long>(g_logTailOffset), SEEK_SET);

    char buf[8192];
    int linesThisPulse = 0;
    constexpr int kMaxLinesPerPulse = 50000;
    std::string myName;
    if (auto pChar = GetCharInfo()) {
        if (pChar->Name[0]) myName = pChar->Name;
    }

    while (linesThisPulse < kMaxLinesPerPulse && std::fgets(buf, sizeof(buf), g_logTailFile)) {
        ++linesThisPulse;
        g_logTailLines.fetch_add(1, std::memory_order_relaxed);
        // Trim CR/LF only. ProcessLine strips the EQ timestamp itself.
        size_t n = std::strlen(buf);
        while (n > 0 && (buf[n - 1] == '\n' || buf[n - 1] == '\r')) buf[--n] = 0;
        if (n == 0) continue;

        // Do NOT call ShouldDropRawLineDuplicate here. While log tailing is
        // enabled we skip chat-callback parsing, so the log is the single DPS
        // source and identical same-amount melee hits must remain countable.
        if (ProcessLine(buf, myName)) {
            g_logTailMatched.fetch_add(1, std::memory_order_relaxed);
        }
    }

    long pos = std::ftell(g_logTailFile);
    if (pos >= 0) g_logTailOffset = static_cast<uint64_t>(pos);
}


} // anonymous namespace

// ----------------------------------------------------------------------------
// Plugin entry points
// ----------------------------------------------------------------------------

PLUGIN_API void InitializePlugin() {
    DebugSpewAlways("MQ2HealParse: InitializePlugin");
    pHealParseType = new MQ2HealParseType;
    AddMQ2Data("HealParse", dataHealParse);
    AddCommand("/healparse", Cmd_HealParse);
    HP_LoadPlayerClassCache();
    HP_LoadMobIconCache();
    HP_LoadDpsHistory();
    HP_LoadHealHistory();
    HP_LoadPetOwners();
    HP_LoadBurnTriggers();
    WriteChatf("\ag[HealParse]\ax loaded. UI is hidden by default. Type \at/healparse ui on\ax to open it, or \at/healparse overlay on\ax for mini.");
}

PLUGIN_API void ShutdownPlugin() {
    DebugSpewAlways("MQ2HealParse: ShutdownPlugin");
    { std::lock_guard<std::mutex> hk(g_completedDpsMutex); HP_SaveDpsHistoryUnlocked(); }
    { std::lock_guard<std::mutex> hk(g_completedHealFightsMutex); HP_SaveHealHistoryUnlocked(); }
    { std::lock_guard<std::mutex> lk(g_statsMutex); HP_SavePetOwnersUnlocked(); }
    HP_SaveBurnTriggers();
    { std::lock_guard<std::mutex> ck(g_playerClassCacheMutex); HP_SavePlayerClassCacheUnlocked(); }
    HP_SaveMobIconCacheIfDirty();
    HP_ReleaseDemonIconTexture();
    CloseLogTailer();
    RemoveCommand("/healparse");
    RemoveMQ2Data("HealParse");
    delete pHealParseType;
    pHealParseType = nullptr;
}


// ----------------------------------------------------------------------------
// Dual chat-source capture.
//
// OnIncomingChat by itself can miss combat text on some clients/servers before
// it is finally written to the visible/log chat stream. GamParse reads the final
// EQ log, so to match it we also listen to OnWriteChatColor. Because many lines
// can appear in BOTH callbacks, we use a very short cross-source raw-line de-dupe
// window so the plugin can take the earliest source without double-counting.
// Same-source identical damage lines are still counted; they are valid EQ log events.
// ----------------------------------------------------------------------------
struct HP_RecentRawLine {
    int64_t atMs = 0;
    std::string source;
};

std::unordered_map<std::string, HP_RecentRawLine> g_recentRawLines;
std::mutex g_recentRawLinesMutex;
constexpr int64_t kRawLineDedupMs = 25;

// Only drop the same raw line when it arrives from the OTHER chat callback
// inside the tiny callback overlap window. Do not drop same-source identical
// combat lines: Project Lazarus can legitimately print the exact same line
// several times in the same second, especially swarm pets and multi-hit skills
// such as "Ayehop`s pet hits ... for 201" or "Handy hit ... for 300".
bool ShouldDropRawLineDuplicate(const char* raw, const char* source)
{
    if (!raw || !*raw) return true;
    const int64_t now = NowMs();
    std::string key = StripLogTimestamp(raw);
    RTrim(key);
    if (key.empty()) return true;

    const std::string src = source ? source : "";

    std::lock_guard<std::mutex> lk(g_recentRawLinesMutex);
    auto it = g_recentRawLines.find(key);
    if (it != g_recentRawLines.end()) {
        const int64_t age = now - it->second.atMs;
        const bool differentSource = !src.empty() && !it->second.source.empty() && src != it->second.source;

        // This is the OnIncomingChat + OnWriteChatColor duplicate path.
        // Same-source duplicates are real log events and must be counted to
        // match GamParse.
        if (differentSource && age >= 0 && age < kRawLineDedupMs) {
            it->second.atMs = now;
            it->second.source = src;
            g_linesDeduped.fetch_add(1, std::memory_order_relaxed);
            return true;
        }

        // Keep the freshest source/time for cleanup and the next callback pair.
        it->second.atMs = now;
        it->second.source = src;
        return false;
    }

    g_recentRawLines[key] = { now, src };

    if (g_recentRawLines.size() > 8192) {
        for (auto p = g_recentRawLines.begin(); p != g_recentRawLines.end(); ) {
            if ((now - p->second.atMs) > 3000) p = g_recentRawLines.erase(p);
            else ++p;
        }
    }
    return false;
}

std::string HP_CurrentCharName()
{
    if (auto pChar = GetCharInfo()) {
        if (pChar->Name[0]) return pChar->Name;
    }
    return std::string();
}

// Burn timer rules should only react to MQ2/E3 relay-style lines, not normal
// EverQuest combat/spell log lines.  The source gate in ProcessPluginChatLine
// already limits this to OnWriteChatColor; this extra text gate keeps ordinary
// EQ chat such as "Name begins to cast a spell" from starting burn timers.
bool HP_IsMqBurnTimerWindowLine(const char* line)
{
    if (!line || !*line) return false;

    // E3/MQ relay windows usually prefix messages with these tags.
    if (FindSubstr(line, "[E3]") != nullptr) return true;
    if (FindSubstr(line, "[MQ") != nullptr) return true;
    if (FindSubstr(line, "MQ2") != nullptr) return true;

    // E3 command relay format: "Dorfus => Dorias : /nowcast ...".
    if (FindSubstr(line, "=>") != nullptr) return true;

    return false;
}




bool ProcessPluginChatLine(const char* Line, const char* source)
{
    if (!g_enabled.load()) return false;
    if (!Line || !*Line) return false;
    if (g_auditEnabled.load()) g_auditCurrentSource = source ? source : "";

    // Skip our own emissions / MQ helper lines so the bridge never feeds back.
    if (FindSubstr(Line, "/hpevt|") != nullptr) return false;
    if (FindSubstr(Line, "[HealParse]") != nullptr) return false;
    if (FindSubstr(Line, "[HealTracker]") != nullptr) return false;

    const std::string myName = HP_CurrentCharName();

    // Burn timers are intentionally driven from the visible MQ2/E3 chat window only.
    // Do NOT scan the EQ log tailer or the early OnIncomingChat callback for burns.
    // This prevents one burn announcement from starting twice and prevents old EQ
    // log/backlog lines from creating stale duplicate countdowns.
    if (source && _stricmp(source, "OnWriteChatColor") == 0 && HP_IsMqBurnTimerWindowLine(Line))
        HP_CheckBurnTriggers(Line, myName);

    // When the C++ log tailer is active, the EQ log is the single source of
    // DPS truth, matching GamParse and preventing chat+log double counts.
    // Burn timers were already checked above from the live MQ2 window line.
    if (g_logTailEnabled.load() && !g_logTailPath.empty()) return false;

    if (ShouldDropRawLineDuplicate(Line, source)) return false;

    bool consumed = ProcessLine(Line, myName);
    if (consumed && g_debug.load()) {
        WriteChatf("\ay[HP-DBG]\ax matched: %.80s", Line);
    }
    return consumed;
}


// OnIncomingChat receives every chat line as it arrives, before it's added to
// the chatbuffer. This is BEFORE Lua's mq.event handlers see it, and also
// before the log file is written -- so we beat the lua tailer to the parse
// by anywhere from 5ms to 50ms per line. In a 54-man raid that means we can
// process thousands of lines per second without falling behind.
//
// Color is the chat-color code. We don't filter on color; we filter on text.
PLUGIN_API bool OnIncomingChat(const char* Line, DWORD /*Color*/) {
    g_linesFromIncoming.fetch_add(1, std::memory_order_relaxed);
    ProcessPluginChatLine(Line, "OnIncomingChat");

    // Return false so MQ continues normal chat handling. We're a tap, not a
    // filter.
    return false;
}

// OnWriteChatColor sees lines at the final chat/log write stage. This catches
// combat lines that do not consistently fire OnIncomingChat on some clients.
// We return 0 so nothing is filtered or redirected.
PLUGIN_API DWORD OnWriteChatColor(const char* Line, DWORD /*Color*/, DWORD /*Filter*/) {
    g_linesFromWriteChat.fetch_add(1, std::memory_order_relaxed);
    ProcessPluginChatLine(Line, "OnWriteChatColor");
    return 0;
}

// Plugin-owned ImGui mini DPS overlay. The Lua full UI remains separate.
PLUGIN_API void OnUpdateImGui() {
    DrawHealParseLiveDpsOverlayOncePerFrame();
    DrawHealParseAfterFightPopupOncePerFrame();
    DrawHealParseFullUiOncePerFrame();
}

// Compatibility fallback for MQ builds that render plugin overlays from HUD draw.
PLUGIN_API void OnDrawHUD() {
    DrawHealParseLiveDpsOverlayOncePerFrame();
    DrawHealParseAfterFightPopupOncePerFrame();
    DrawHealParseFullUiOncePerFrame();
}

// Saves history/cache files away from the kill/archive path.  This writes at
// most one history file per pass, waits a few seconds after the last archive,
// and skips while a live DPS fight is active.
static void HP_MaybeSaveDeferredHistories()
{
    int64_t now = NowMs();
    int64_t dirtyAt = g_historyDirtyAtMs.load();
    if (dirtyAt <= 0 || now - dirtyAt < kDeferredHistorySaveDelayMs) return;
    if (now - g_lastDeferredHistorySaveMs.load() < kDeferredHistorySaveGapMs) return;

    {
        std::lock_guard<std::mutex> lk(g_liveDpsMutex);
        if (!g_liveDps.mob.empty()) return;
    }

    if (g_dpsHistoryDirty.exchange(false)) {
        std::lock_guard<std::mutex> hk(g_completedDpsMutex);
        HP_SaveDpsHistoryUnlocked();
        g_lastDeferredHistorySaveMs.store(now);
        return;
    }

    if (g_healHistoryDirty.exchange(false)) {
        std::lock_guard<std::mutex> hk(g_completedHealFightsMutex);
        HP_SaveHealHistoryUnlocked();
        g_lastDeferredHistorySaveMs.store(now);
        return;
    }

    HP_SaveMobIconCacheIfDirty();
    g_historyDirtyAtMs.store(0);
}

// Pulse fires every frame. We use it for periodic cache cleanup so the
// recent-spell-cast cache doesn't grow without bound during long raids.
PLUGIN_API void OnPulse() {
    TailPluginLog();

    // Archive timed-out fights from the plugin pulse path so completed fights
    // and the after-fight popup happen automatically, even when the full UI is closed.
    HP_MaybeArchiveTimedOutLiveDps();
    HP_MaybeClearTimedOutLiveTank();
    HP_MaybeSaveDeferredHistories();

    static int64_t lastSweep = 0;
    int64_t now = NowMs();
    if (now - lastSweep < 30000) return; // every 30s
    lastSweep = now;

    std::lock_guard<std::mutex> lk(g_statsMutex);
    for (auto it = g_recentSpellCasts.begin(); it != g_recentSpellCasts.end();) {
        if (now - it->second.atMs > 120000) it = g_recentSpellCasts.erase(it);
        else ++it;
    }
}

// Zone change -- clear caches that should not survive across zones.
PLUGIN_API void OnZoned() {
    {
        std::lock_guard<std::mutex> lk(g_statsMutex);
        g_recentSpellCasts.clear();
    }
    // Pet-owner cache has its own mutex; clear separately to avoid
    // holding two locks at once.
    ClearPetOwnerCache();
    // Drop any stale events the bridge didn't drain before the zone.
    {
        {
            std::lock_guard<std::mutex> lk(g_damageBatchMutex);
            g_damageBatch.clear();
            g_damageBatchOrder.clear();
        }
        std::lock_guard<std::mutex> lk(g_eventQueueMutex);
        g_eventQueue.clear();
    }
    {
        std::lock_guard<std::mutex> lk(g_recentRawLinesMutex);
        g_recentRawLines.clear();
    }
    // Keep aggregate counters and knownChars across zones; the Lua's fight
    // boundary handles per-fight resets.
}
