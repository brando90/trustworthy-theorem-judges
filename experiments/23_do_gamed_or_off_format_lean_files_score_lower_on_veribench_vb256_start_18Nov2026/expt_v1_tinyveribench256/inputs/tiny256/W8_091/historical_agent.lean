import Mathlib
namespace Agent

/-!
# Cross-site scripting example

A pure translation of the Python application, with an executable recognizer for
exactly the regular expressions in the source. Regex search is unanchored;
repetition enumerates all possible endpoints (so backtracking is preserved).
The character classes use Unicode 15.0, the Unicode version of Python in this
environment. Case-insensitive ASCII literals include Python's four additional
Unicode equivalents. No HTML parser or browser security claim is assumed.

Contexts are insertion-ordered dictionaries after Python `str` conversion. Thus
arbitrary Python values are represented by their observable string, including
`5` for the result count. Application state is explicit and is never modified
by the handlers. The templates really have *three* braces, whereas the renderer
replaces *two*: one pair of braces remains around each inserted value.
-/

namespace CrossSiteScripting

abbrev Context := List (String × String)

structure WebApplication where
  user_sessions : Context := []
  comments : List String := []
  search_history : List String := []
  deriving Repr, BEq, DecidableEq

/-- Python's character-level `html.escape(..., quote=True)`. -/
def escapeChar (c : Char) : List Char :=
  if c = '&' then "&amp;".toList
  else if c = '<' then "&lt;".toList
  else if c = '>' then "&gt;".toList
  else if c = '"' then "&quot;".toList
  else if c = '\'' then "&#x27;".toList
  else [c]

def htmlEscape (s : String) : String := String.mk (s.toList.flatMap escapeChar)

def placeholder (key : String) : String := "{{" ++ key ++ "}}"

def substitute (template : String) (entry : String × String) : String :=
  template.replace (placeholder entry.1) entry.2

def render_template (_app : WebApplication) (template : String) (context : Context) : String :=
  context.foldl substitute template

def escapeContext (context : Context) : Context :=
  context.map fun (k, v) => (k, htmlEscape v)

def safe_render_template (app : WebApplication) (template : String) (context : Context) : String :=
  render_template app template (escapeContext context)

/-- Maximal ranges of Unicode alphanumeric characters, plus underscore.
This is Python's Unicode `\w`, not JavaScript's ASCII `\w`. -/
def wordRanges : List (Nat × Nat) :=
  [(48, 57),
   (65, 90),
   (95, 95),
   (97, 122),
   (170, 170),
   (178, 179),
   (181, 181),
   (185, 186),
   (188, 190),
   (192, 214),
   (216, 246),
   (248, 705),
   (710, 721),
   (736, 740),
   (748, 748),
   (750, 750),
   (880, 884),
   (886, 887),
   (890, 893),
   (895, 895),
   (902, 902),
   (904, 906),
   (908, 908),
   (910, 929),
   (931, 1013),
   (1015, 1153),
   (1162, 1327),
   (1329, 1366),
   (1369, 1369),
   (1376, 1416),
   (1488, 1514),
   (1519, 1522),
   (1568, 1610),
   (1632, 1641),
   (1646, 1647),
   (1649, 1747),
   (1749, 1749),
   (1765, 1766),
   (1774, 1788),
   (1791, 1791),
   (1808, 1808),
   (1810, 1839),
   (1869, 1957),
   (1969, 1969),
   (1984, 2026),
   (2036, 2037),
   (2042, 2042),
   (2048, 2069),
   (2074, 2074),
   (2084, 2084),
   (2088, 2088),
   (2112, 2136),
   (2144, 2154),
   (2160, 2183),
   (2185, 2190),
   (2208, 2249),
   (2308, 2361),
   (2365, 2365),
   (2384, 2384),
   (2392, 2401),
   (2406, 2415),
   (2417, 2432),
   (2437, 2444),
   (2447, 2448),
   (2451, 2472),
   (2474, 2480),
   (2482, 2482),
   (2486, 2489),
   (2493, 2493),
   (2510, 2510),
   (2524, 2525),
   (2527, 2529),
   (2534, 2545),
   (2548, 2553),
   (2556, 2556),
   (2565, 2570),
   (2575, 2576),
   (2579, 2600),
   (2602, 2608),
   (2610, 2611),
   (2613, 2614),
   (2616, 2617),
   (2649, 2652),
   (2654, 2654),
   (2662, 2671),
   (2674, 2676),
   (2693, 2701),
   (2703, 2705),
   (2707, 2728),
   (2730, 2736),
   (2738, 2739),
   (2741, 2745),
   (2749, 2749),
   (2768, 2768),
   (2784, 2785),
   (2790, 2799),
   (2809, 2809),
   (2821, 2828),
   (2831, 2832),
   (2835, 2856),
   (2858, 2864),
   (2866, 2867),
   (2869, 2873),
   (2877, 2877),
   (2908, 2909),
   (2911, 2913),
   (2918, 2927),
   (2929, 2935),
   (2947, 2947),
   (2949, 2954),
   (2958, 2960),
   (2962, 2965),
   (2969, 2970),
   (2972, 2972),
   (2974, 2975),
   (2979, 2980),
   (2984, 2986),
   (2990, 3001),
   (3024, 3024),
   (3046, 3058),
   (3077, 3084),
   (3086, 3088),
   (3090, 3112),
   (3114, 3129),
   (3133, 3133),
   (3160, 3162),
   (3165, 3165),
   (3168, 3169),
   (3174, 3183),
   (3192, 3198),
   (3200, 3200),
   (3205, 3212),
   (3214, 3216),
   (3218, 3240),
   (3242, 3251),
   (3253, 3257),
   (3261, 3261),
   (3293, 3294),
   (3296, 3297),
   (3302, 3311),
   (3313, 3314),
   (3332, 3340),
   (3342, 3344),
   (3346, 3386),
   (3389, 3389),
   (3406, 3406),
   (3412, 3414),
   (3416, 3425),
   (3430, 3448),
   (3450, 3455),
   (3461, 3478),
   (3482, 3505),
   (3507, 3515),
   (3517, 3517),
   (3520, 3526),
   (3558, 3567),
   (3585, 3632),
   (3634, 3635),
   (3648, 3654),
   (3664, 3673),
   (3713, 3714),
   (3716, 3716),
   (3718, 3722),
   (3724, 3747),
   (3749, 3749),
   (3751, 3760),
   (3762, 3763),
   (3773, 3773),
   (3776, 3780),
   (3782, 3782),
   (3792, 3801),
   (3804, 3807),
   (3840, 3840),
   (3872, 3891),
   (3904, 3911),
   (3913, 3948),
   (3976, 3980),
   (4096, 4138),
   (4159, 4169),
   (4176, 4181),
   (4186, 4189),
   (4193, 4193),
   (4197, 4198),
   (4206, 4208),
   (4213, 4225),
   (4238, 4238),
   (4240, 4249),
   (4256, 4293),
   (4295, 4295),
   (4301, 4301),
   (4304, 4346),
   (4348, 4680),
   (4682, 4685),
   (4688, 4694),
   (4696, 4696),
   (4698, 4701),
   (4704, 4744),
   (4746, 4749),
   (4752, 4784),
   (4786, 4789),
   (4792, 4798),
   (4800, 4800),
   (4802, 4805),
   (4808, 4822),
   (4824, 4880),
   (4882, 4885),
   (4888, 4954),
   (4969, 4988),
   (4992, 5007),
   (5024, 5109),
   (5112, 5117),
   (5121, 5740),
   (5743, 5759),
   (5761, 5786),
   (5792, 5866),
   (5870, 5880),
   (5888, 5905),
   (5919, 5937),
   (5952, 5969),
   (5984, 5996),
   (5998, 6000),
   (6016, 6067),
   (6103, 6103),
   (6108, 6108),
   (6112, 6121),
   (6128, 6137),
   (6160, 6169),
   (6176, 6264),
   (6272, 6276),
   (6279, 6312),
   (6314, 6314),
   (6320, 6389),
   (6400, 6430),
   (6470, 6509),
   (6512, 6516),
   (6528, 6571),
   (6576, 6601),
   (6608, 6618),
   (6656, 6678),
   (6688, 6740),
   (6784, 6793),
   (6800, 6809),
   (6823, 6823),
   (6917, 6963),
   (6981, 6988),
   (6992, 7001),
   (7043, 7072),
   (7086, 7141),
   (7168, 7203),
   (7232, 7241),
   (7245, 7293),
   (7296, 7304),
   (7312, 7354),
   (7357, 7359),
   (7401, 7404),
   (7406, 7411),
   (7413, 7414),
   (7418, 7418),
   (7424, 7615),
   (7680, 7957),
   (7960, 7965),
   (7968, 8005),
   (8008, 8013),
   (8016, 8023),
   (8025, 8025),
   (8027, 8027),
   (8029, 8029),
   (8031, 8061),
   (8064, 8116),
   (8118, 8124),
   (8126, 8126),
   (8130, 8132),
   (8134, 8140),
   (8144, 8147),
   (8150, 8155),
   (8160, 8172),
   (8178, 8180),
   (8182, 8188),
   (8304, 8305),
   (8308, 8313),
   (8319, 8329),
   (8336, 8348),
   (8450, 8450),
   (8455, 8455),
   (8458, 8467),
   (8469, 8469),
   (8473, 8477),
   (8484, 8484),
   (8486, 8486),
   (8488, 8488),
   (8490, 8493),
   (8495, 8505),
   (8508, 8511),
   (8517, 8521),
   (8526, 8526),
   (8528, 8585),
   (9312, 9371),
   (9450, 9471),
   (10102, 10131),
   (11264, 11492),
   (11499, 11502),
   (11506, 11507),
   (11517, 11517),
   (11520, 11557),
   (11559, 11559),
   (11565, 11565),
   (11568, 11623),
   (11631, 11631),
   (11648, 11670),
   (11680, 11686),
   (11688, 11694),
   (11696, 11702),
   (11704, 11710),
   (11712, 11718),
   (11720, 11726),
   (11728, 11734),
   (11736, 11742),
   (11823, 11823),
   (12293, 12295),
   (12321, 12329),
   (12337, 12341),
   (12344, 12348),
   (12353, 12438),
   (12445, 12447),
   (12449, 12538),
   (12540, 12543),
   (12549, 12591),
   (12593, 12686),
   (12690, 12693),
   (12704, 12735),
   (12784, 12799),
   (12832, 12841),
   (12872, 12879),
   (12881, 12895),
   (12928, 12937),
   (12977, 12991),
   (13312, 19903),
   (19968, 42124),
   (42192, 42237),
   (42240, 42508),
   (42512, 42539),
   (42560, 42606),
   (42623, 42653),
   (42656, 42735),
   (42775, 42783),
   (42786, 42888),
   (42891, 42954),
   (42960, 42961),
   (42963, 42963),
   (42965, 42969),
   (42994, 43009),
   (43011, 43013),
   (43015, 43018),
   (43020, 43042),
   (43056, 43061),
   (43072, 43123),
   (43138, 43187),
   (43216, 43225),
   (43250, 43255),
   (43259, 43259),
   (43261, 43262),
   (43264, 43301),
   (43312, 43334),
   (43360, 43388),
   (43396, 43442),
   (43471, 43481),
   (43488, 43492),
   (43494, 43518),
   (43520, 43560),
   (43584, 43586),
   (43588, 43595),
   (43600, 43609),
   (43616, 43638),
   (43642, 43642),
   (43646, 43695),
   (43697, 43697),
   (43701, 43702),
   (43705, 43709),
   (43712, 43712),
   (43714, 43714),
   (43739, 43741),
   (43744, 43754),
   (43762, 43764),
   (43777, 43782),
   (43785, 43790),
   (43793, 43798),
   (43808, 43814),
   (43816, 43822),
   (43824, 43866),
   (43868, 43881),
   (43888, 44002),
   (44016, 44025),
   (44032, 55203),
   (55216, 55238),
   (55243, 55291),
   (63744, 64109),
   (64112, 64217),
   (64256, 64262),
   (64275, 64279),
   (64285, 64285),
   (64287, 64296),
   (64298, 64310),
   (64312, 64316),
   (64318, 64318),
   (64320, 64321),
   (64323, 64324),
   (64326, 64433),
   (64467, 64829),
   (64848, 64911),
   (64914, 64967),
   (65008, 65019),
   (65136, 65140),
   (65142, 65276),
   (65296, 65305),
   (65313, 65338),
   (65345, 65370),
   (65382, 65470),
   (65474, 65479),
   (65482, 65487),
   (65490, 65495),
   (65498, 65500),
   (65536, 65547),
   (65549, 65574),
   (65576, 65594),
   (65596, 65597),
   (65599, 65613),
   (65616, 65629),
   (65664, 65786),
   (65799, 65843),
   (65856, 65912),
   (65930, 65931),
   (66176, 66204),
   (66208, 66256),
   (66273, 66299),
   (66304, 66339),
   (66349, 66378),
   (66384, 66421),
   (66432, 66461),
   (66464, 66499),
   (66504, 66511),
   (66513, 66517),
   (66560, 66717),
   (66720, 66729),
   (66736, 66771),
   (66776, 66811),
   (66816, 66855),
   (66864, 66915),
   (66928, 66938),
   (66940, 66954),
   (66956, 66962),
   (66964, 66965),
   (66967, 66977),
   (66979, 66993),
   (66995, 67001),
   (67003, 67004),
   (67072, 67382),
   (67392, 67413),
   (67424, 67431),
   (67456, 67461),
   (67463, 67504),
   (67506, 67514),
   (67584, 67589),
   (67592, 67592),
   (67594, 67637),
   (67639, 67640),
   (67644, 67644),
   (67647, 67669),
   (67672, 67702),
   (67705, 67742),
   (67751, 67759),
   (67808, 67826),
   (67828, 67829),
   (67835, 67867),
   (67872, 67897),
   (67968, 68023),
   (68028, 68047),
   (68050, 68096),
   (68112, 68115),
   (68117, 68119),
   (68121, 68149),
   (68160, 68168),
   (68192, 68222),
   (68224, 68255),
   (68288, 68295),
   (68297, 68324),
   (68331, 68335),
   (68352, 68405),
   (68416, 68437),
   (68440, 68466),
   (68472, 68497),
   (68521, 68527),
   (68608, 68680),
   (68736, 68786),
   (68800, 68850),
   (68858, 68899),
   (68912, 68921),
   (69216, 69246),
   (69248, 69289),
   (69296, 69297),
   (69376, 69415),
   (69424, 69445),
   (69457, 69460),
   (69488, 69505),
   (69552, 69579),
   (69600, 69622),
   (69635, 69687),
   (69714, 69743),
   (69745, 69746),
   (69749, 69749),
   (69763, 69807),
   (69840, 69864),
   (69872, 69881),
   (69891, 69926),
   (69942, 69951),
   (69956, 69956),
   (69959, 69959),
   (69968, 70002),
   (70006, 70006),
   (70019, 70066),
   (70081, 70084),
   (70096, 70106),
   (70108, 70108),
   (70113, 70132),
   (70144, 70161),
   (70163, 70187),
   (70207, 70208),
   (70272, 70278),
   (70280, 70280),
   (70282, 70285),
   (70287, 70301),
   (70303, 70312),
   (70320, 70366),
   (70384, 70393),
   (70405, 70412),
   (70415, 70416),
   (70419, 70440),
   (70442, 70448),
   (70450, 70451),
   (70453, 70457),
   (70461, 70461),
   (70480, 70480),
   (70493, 70497),
   (70656, 70708),
   (70727, 70730),
   (70736, 70745),
   (70751, 70753),
   (70784, 70831),
   (70852, 70853),
   (70855, 70855),
   (70864, 70873),
   (71040, 71086),
   (71128, 71131),
   (71168, 71215),
   (71236, 71236),
   (71248, 71257),
   (71296, 71338),
   (71352, 71352),
   (71360, 71369),
   (71424, 71450),
   (71472, 71483),
   (71488, 71494),
   (71680, 71723),
   (71840, 71922),
   (71935, 71942),
   (71945, 71945),
   (71948, 71955),
   (71957, 71958),
   (71960, 71983),
   (71999, 71999),
   (72001, 72001),
   (72016, 72025),
   (72096, 72103),
   (72106, 72144),
   (72161, 72161),
   (72163, 72163),
   (72192, 72192),
   (72203, 72242),
   (72250, 72250),
   (72272, 72272),
   (72284, 72329),
   (72349, 72349),
   (72368, 72440),
   (72704, 72712),
   (72714, 72750),
   (72768, 72768),
   (72784, 72812),
   (72818, 72847),
   (72960, 72966),
   (72968, 72969),
   (72971, 73008),
   (73030, 73030),
   (73040, 73049),
   (73056, 73061),
   (73063, 73064),
   (73066, 73097),
   (73112, 73112),
   (73120, 73129),
   (73440, 73458),
   (73474, 73474),
   (73476, 73488),
   (73490, 73523),
   (73552, 73561),
   (73648, 73648),
   (73664, 73684),
   (73728, 74649),
   (74752, 74862),
   (74880, 75075),
   (77712, 77808),
   (77824, 78895),
   (78913, 78918),
   (82944, 83526),
   (92160, 92728),
   (92736, 92766),
   (92768, 92777),
   (92784, 92862),
   (92864, 92873),
   (92880, 92909),
   (92928, 92975),
   (92992, 92995),
   (93008, 93017),
   (93019, 93025),
   (93027, 93047),
   (93053, 93071),
   (93760, 93846),
   (93952, 94026),
   (94032, 94032),
   (94099, 94111),
   (94176, 94177),
   (94179, 94179),
   (94208, 100343),
   (100352, 101589),
   (101632, 101640),
   (110576, 110579),
   (110581, 110587),
   (110589, 110590),
   (110592, 110882),
   (110898, 110898),
   (110928, 110930),
   (110933, 110933),
   (110948, 110951),
   (110960, 111355),
   (113664, 113770),
   (113776, 113788),
   (113792, 113800),
   (113808, 113817),
   (119488, 119507),
   (119520, 119539),
   (119648, 119672),
   (119808, 119892),
   (119894, 119964),
   (119966, 119967),
   (119970, 119970),
   (119973, 119974),
   (119977, 119980),
   (119982, 119993),
   (119995, 119995),
   (119997, 120003),
   (120005, 120069),
   (120071, 120074),
   (120077, 120084),
   (120086, 120092),
   (120094, 120121),
   (120123, 120126),
   (120128, 120132),
   (120134, 120134),
   (120138, 120144),
   (120146, 120485),
   (120488, 120512),
   (120514, 120538),
   (120540, 120570),
   (120572, 120596),
   (120598, 120628),
   (120630, 120654),
   (120656, 120686),
   (120688, 120712),
   (120714, 120744),
   (120746, 120770),
   (120772, 120779),
   (120782, 120831),
   (122624, 122654),
   (122661, 122666),
   (122928, 122989),
   (123136, 123180),
   (123191, 123197),
   (123200, 123209),
   (123214, 123214),
   (123536, 123565),
   (123584, 123627),
   (123632, 123641),
   (124112, 124139),
   (124144, 124153),
   (124896, 124902),
   (124904, 124907),
   (124909, 124910),
   (124912, 124926),
   (124928, 125124),
   (125127, 125135),
   (125184, 125251),
   (125259, 125259),
   (125264, 125273),
   (126065, 126123),
   (126125, 126127),
   (126129, 126132),
   (126209, 126253),
   (126255, 126269),
   (126464, 126467),
   (126469, 126495),
   (126497, 126498),
   (126500, 126500),
   (126503, 126503),
   (126505, 126514),
   (126516, 126519),
   (126521, 126521),
   (126523, 126523),
   (126530, 126530),
   (126535, 126535),
   (126537, 126537),
   (126539, 126539),
   (126541, 126543),
   (126545, 126546),
   (126548, 126548),
   (126551, 126551),
   (126553, 126553),
   (126555, 126555),
   (126557, 126557),
   (126559, 126559),
   (126561, 126562),
   (126564, 126564),
   (126567, 126570),
   (126572, 126578),
   (126580, 126583),
   (126585, 126588),
   (126590, 126590),
   (126592, 126601),
   (126603, 126619),
   (126625, 126627),
   (126629, 126633),
   (126635, 126651),
   (127232, 127244),
   (130032, 130041),
   (131072, 173791),
   (173824, 177977),
   (177984, 178205),
   (178208, 183969),
   (183984, 191456),
   (194560, 195101),
   (196608, 201546),
   (201552, 205743)]

def wordChar (c : Char) : Bool :=
  wordRanges.any fun (lo, hi) => lo ≤ c.toNat && c.toNat ≤ hi

def spaceChar (c : Char) : Bool :=
  [9, 10, 11, 12, 13, 28, 29, 30, 31, 32, 133, 160, 5760,
   8192, 8193, 8194, 8195, 8196, 8197, 8198, 8199, 8200, 8201, 8202,
   8232, 8233, 8239, 8287, 12288].contains c.toNat

def hexChar (c : Char) : Bool :=
  ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')

/-- Canonicalization sufficient for Python IGNORECASE on ASCII literals. -/
def regexLower (c : Char) : Char :=
  if c.toNat = 304 || c.toNat = 305 then 'i'
  else if c.toNat = 383 then 's'
  else if c.toNat = 8490 then 'k'
  else c.toLower

inductive Repeat where
  | one | star | plus | optional
  deriving Repr, BEq, DecidableEq

structure Piece where
  accepts : Char → Bool
  quantifier : Repeat := .one

abbrev Regex := List Piece

/-- All endpoints of a possibly empty run; no greedy-choice approximation. -/
def runEnds (accepts : Char → Bool) : List Char → List (List Char)
  | [] => [[]]
  | c :: cs => (c :: cs) :: (if accepts c then runEnds accepts cs else [])

def consume (p : Piece) (input : List Char) : List (List Char) :=
  match p.quantifier with
  | .one => match input with
    | [] => []
    | c :: cs => if p.accepts c then [cs] else []
  | .star => runEnds p.accepts input
  | .plus => match input with
    | [] => []
    | c :: cs => if p.accepts c then runEnds p.accepts cs else []
  | .optional => input :: (match input with
    | [] => []
    | c :: cs => if p.accepts c then [cs] else [])

def matchesHere : Regex → List Char → Bool
  | [], _ => true
  | p :: ps, input => (consume p input).any (matchesHere ps)

def searchChars (r : Regex) : List Char → Bool
  | [] => matchesHere r []
  | c :: cs => matchesHere r (c :: cs) || searchChars r cs

def regexSearch (r : Regex) (s : String) : Bool := searchChars r s.toList

def literal (s : String) (ignoreCase : Bool := false) : Regex :=
  s.toList.map fun c => ⟨(fun d => if ignoreCase then regexLower c == regexLower d else c == d), .one⟩

def ci (s : String) : Regex := literal s true

def notGT : Piece := ⟨(· != '>'), .star⟩
def spaces : Piece := ⟨spaceChar, .star⟩
def eventHandler : Regex := ci "on" ++ [⟨wordChar, .plus⟩, spaces] ++ ci "="
def openingTag (tag : String) : Regex := ci ("<" ++ tag) ++ [notGT] ++ ci ">"
def tagEvent (tag : String) : Regex := ci ("<" ++ tag) ++ [notGT] ++ eventHandler

/-- Each returned pattern string is exactly the original Python regex text. -/
def scriptPatterns : List (String × Regex) :=
  [("<script[^>]*>.*?</script>", ci "<script" ++ [notGT] ++ ci ">" ++
      [⟨(· != '\n'), .star⟩] ++ ci "</script>"),
   ("javascript:", ci "javascript:"),
   ("on\\w+\\s*=", eventHandler),
   ("<iframe[^>]*>", openingTag "iframe"),
   ("<object[^>]*>", openingTag "object"),
   ("<embed[^>]*>", openingTag "embed"),
   ("<form[^>]*>", openingTag "form"),
   ("<input[^>]*>", openingTag "input"),
   ("<textarea[^>]*>", openingTag "textarea"),
   ("<select[^>]*>", openingTag "select"),
   ("<link[^>]*>", openingTag "link"),
   ("<meta[^>]*>", openingTag "meta"),
   ("<style[^>]*>", openingTag "style"),
   ("<svg[^>]*>", openingTag "svg"),
   ("<img[^>]*on\\w+\\s*=", tagEvent "img"),
   ("<a[^>]*href\\s*=\\s*[\"\\']javascript:", ci "<a" ++ [notGT] ++ ci "href" ++
      [spaces] ++ ci "=" ++ [spaces, ⟨(fun c => c == '\'' || c == '"'), .one⟩] ++ ci "javascript:"),
   ("<div[^>]*on\\w+\\s*=", tagEvent "div"),
   ("<span[^>]*on\\w+\\s*=", tagEvent "span"),
   ("<p[^>]*on\\w+\\s*=", tagEvent "p")]

def encodedPatterns : List (String × Regex) :=
  [("&#x?[0-9a-fA-F]+;", literal "&#" ++ [⟨(· == 'x'), .optional⟩, ⟨hexChar, .plus⟩] ++ literal ";"),
   ("%[0-9a-fA-F]{2}", literal "%" ++ List.replicate 2 ⟨hexChar, .one⟩),
   ("\\\\x[0-9a-fA-F]{2}", literal "\\x" ++ List.replicate 2 ⟨hexChar, .one⟩),
   ("\\\\u[0-9a-fA-F]{4}", literal "\\u" ++ List.replicate 4 ⟨hexChar, .one⟩)]

def detected (patterns : List (String × Regex)) (input : String) : List String :=
  (patterns.filter fun p => regexSearch p.2 input).map Prod.fst

inductive Risk where
  | HIGH | MEDIUM | LOW
  deriving Repr, BEq, DecidableEq

def Risk.asString : Risk → String
  | .HIGH => "HIGH"
  | .MEDIUM => "MEDIUM"
  | .LOW => "LOW"

structure Detection where
  xss_detected : Bool
  script_patterns : List String
  encoded_patterns : List String
  risk_level : Risk
  deriving Repr, BEq, DecidableEq

def detectionFrom (scripts encoded : List String) : Detection :=
  ⟨!scripts.isEmpty || !encoded.isEmpty, scripts, encoded,
   if !scripts.isEmpty then .HIGH else if !encoded.isEmpty then .MEDIUM else .LOW⟩

def detect_xss_patterns (_app : WebApplication) (input : String) : Detection :=
  detectionFrom (detected scriptPatterns input) (detected encodedPatterns input)

/-- Substring search; unlike String.contains this takes a string, not a character. -/
def containsText (s needle : String) : Bool := regexSearch (literal needle) s

/-- The routing words are ASCII and contain no `k`. On these three words,
Python Unicode lowercasing and characterwise ASCII lowercasing have identical
substring results (U+0130 lowercases to `i` followed by a combining dot).
-/
def routeLower (s : String) : String := s.toLower

inductive Scenario where
  | comment | search | profile | generic
  deriving Repr, BEq, DecidableEq

def scenario (input : String) : Scenario :=
  if containsText (routeLower input) "comment" then .comment
  else if containsText (routeLower input) "search" then .search
  else if containsText (routeLower input) "profile" then .profile
  else .generic

def Scenario.typeName : Scenario → String
  | .comment => "comment_xss"
  | .search => "search_xss"
  | .profile => "profile_xss"
  | .generic => "generic_xss"

def commentTemplate : String := "\n    <div class=\"comment\">\n        <p>{{{comment_text}}}</p>\n        <small>Posted by: {{{username}}}</small>\n    </div>\n    "
def searchTemplate : String := "\n    <div class=\"search-results\">\n        <h3>Search results for: {{{search_query}}}</h3>\n        <p>Found {{{result_count}}} results</p>\n    </div>\n    "
def profileTemplate : String := "\n    <div class=\"user-profile\">\n        <h2>{{{display_name}}}</h2>\n        <p>Bio: {{{bio}}}</p>\n        <p>Location: {{{location}}}</p>\n    </div>\n    "
def genericTemplate : String := "<div>{{{user_input}}}</div>"

def Scenario.template : Scenario → String
  | .comment => commentTemplate
  | .search => searchTemplate
  | .profile => profileTemplate
  | .generic => genericTemplate

def Scenario.context : Scenario → String → Context
  | .comment, input => [("comment_text", input), ("username", "user123")]
  | .search, input => [("search_query", input), ("result_count", "5")]
  | .profile, input => [("display_name", input), ("bio", "User bio"), ("location", "Unknown")]
  | .generic, input => [("user_input", input)]

structure Result where
  type : String
  rendered_html : String
  xss_detection : Detection
  vulnerable : Bool
  deriving Repr, BEq, DecidableEq

def unsafe_xss_handling (app : WebApplication) (input : String) : Result :=
  let s := scenario input
  ⟨s.typeName, render_template app s.template (s.context input),
   detect_xss_patterns app input, true⟩

/-- Explicit state-passing interface: the original application is unchanged. -/
def handleState (app : WebApplication) (input : String) : Result × WebApplication :=
  (unsafe_xss_handling app input, app)

/-! ## Unit tests: the ten assertions of `check`, and edge cases -/

def testApp : WebApplication := {}

def inputs : List String :=
  ["Hello, this is a normal comment!",
   "<script>alert('XSS')</script>",
   "<img src=\"x\" onerror=\"alert('XSS')\">",
   "<a href=\"javascript:alert('XSS')\">Click me</a>",
   "<iframe src=\"http://evil.com\"></iframe>",
   "&#x3C;script&#x3E;alert(&#x27;XSS&#x27;)&#x3C;/script&#x3E;",
   "search <script>alert('XSS')</script>",
   "profile <img src=x onerror=alert('XSS')>",
   "comment <script>alert('XSS')</script><img src=x onerror=alert('XSS2')>",
   "<style>body{background:url(\"javascript:alert('XSS')\")}</style>"]

instance : Inhabited Result := ⟨⟨"", "", detectionFrom [] [], false⟩⟩

def check (candidate : WebApplication → String → Result) : Bool :=
  let r := inputs.map (candidate testApp)
  -- Result guarantees the presence of the vulnerable key; Python does not assert its value.
  containsText (r[0]!).rendered_html inputs[0]! &&
  containsText (r[1]!).rendered_html inputs[1]! && (r[1]!).xss_detection.xss_detected &&
  containsText (r[2]!).rendered_html "onerror=" && (r[2]!).xss_detection.xss_detected &&
  containsText (r[3]!).rendered_html "javascript:" && (r[3]!).xss_detection.xss_detected &&
  containsText (r[4]!).rendered_html "<iframe" && (r[4]!).xss_detection.xss_detected &&
  (r[5]!).xss_detection.xss_detected &&
  containsText (r[6]!).type "search_xss" && containsText (r[7]!).type "profile_xss" &&
  containsText (r[8]!).type "comment_xss" && containsText (r[9]!).rendered_html "<style"

example : check unsafe_xss_handling = true := by native_decide
-- Exact test-harness semantics: the field exists even when its value is false.
example : check (fun app s => { unsafe_xss_handling app s with vulnerable := false }) = true := by native_decide
#eval check unsafe_xss_handling
#eval if check unsafe_xss_handling then "All tests passed." else "Candidate failed XSS tests"
#eval inputs.map (unsafe_xss_handling testApp)

example : render_template testApp "{{{x}}}" [("x", "<b>")] = "{<b>}" := by native_decide
example : safe_render_template testApp "{{{x}}}" [("x", "<&\"'>")] =
    "{&lt;&amp;&quot;&#x27;&gt;}" := by native_decide
example : render_template testApp "{{a}}" [("a", "{{b}}"), ("b", "ok")] = "ok" := by native_decide
example : (detect_xss_patterns testApp "<SCRIPT>x</SCRIPT>").risk_level = .HIGH := by native_decide
example : (detect_xss_patterns testApp "<script>x\ny</script>").risk_level = .LOW := by native_decide
example : (detect_xss_patterns testApp "&#X3C;").risk_level = .LOW := by native_decide
example : (detect_xss_patterns testApp "%aF\\x12\\u0041").risk_level = .MEDIUM := by native_decide
example : (detect_xss_patterns testApp "oné =").xss_detected = true := by native_decide
example : (detect_xss_patterns testApp "javaſcript:").xss_detected = true := by native_decide

/-! ## Preconditions and universally quantified properties -/

/-- Every string and every application state is admissible. -/
def Pre (_app : WebApplication) (_input : String) : Prop := True

/-- Ordered, non-sanitizing substitution; the safe variant changes only values. -/
def rendering_prop (app : WebApplication) (template : String) (first later : Context) : Prop :=
  render_template app template (first ++ later) =
    render_template app (render_template app template first) later ∧
  safe_render_template app template first =
    render_template app template (first.map fun (k, v) => (k, htmlEscape v))

theorem rendering_thm (app : WebApplication) (template : String) (first later : Context) :
    rendering_prop app template first later := by
  simp [rendering_prop, render_template, safe_render_template, escapeContext, List.foldl_append]

/-- Escaped values have no raw HTML delimiters or quotes. This is deliberately
not a claim that arbitrary surrounding templates are secure. -/
def escape_prop (input : String) : Prop :=
  '<' ∉ (htmlEscape input).toList ∧ '>' ∉ (htmlEscape input).toList ∧
  '"' ∉ (htmlEscape input).toList ∧ '\'' ∉ (htmlEscape input).toList

theorem escapeChar_clean (c : Char) :
    '<' ∉ escapeChar c ∧ '>' ∉ escapeChar c ∧
    '"' ∉ escapeChar c ∧ '\'' ∉ escapeChar c := by
  unfold escapeChar
  split_ifs <;> simp_all [eq_comm]

theorem escape_thm (input : String) : escape_prop input := by
  have h (d : Char) (hd : d = '<' ∨ d = '>' ∨ d = '"' ∨ d = '\'') :
      d ∉ input.toList.flatMap escapeChar := by
    intro hm
    obtain ⟨c, _, hc⟩ := List.mem_flatMap.mp hm
    rcases hd with rfl | rfl | rfl | rfl
    · exact (escapeChar_clean c).1 hc
    · exact (escapeChar_clean c).2.1 hc
    · exact (escapeChar_clean c).2.2.1 hc
    · exact (escapeChar_clean c).2.2.2 hc
  exact ⟨h '<' (by simp), h '>' (by simp), h '"' (by simp), h '\'' (by simp)⟩

/-- All matches are returned in declaration order. Detection is the disjunction
of the two nonempty lists; script matches take priority for risk. -/
def detection_prop (app : WebApplication) (input : String) : Prop :=
  let d := detect_xss_patterns app input
  d.script_patterns = detected scriptPatterns input ∧
  d.encoded_patterns = detected encodedPatterns input ∧
  (d.xss_detected = true ↔ d.script_patterns ≠ [] ∨ d.encoded_patterns ≠ []) ∧
  (d.risk_level = .HIGH ↔ d.script_patterns ≠ []) ∧
  (d.risk_level = .MEDIUM ↔ d.script_patterns = [] ∧ d.encoded_patterns ≠ []) ∧
  (d.risk_level = .LOW ↔ d.script_patterns = [] ∧ d.encoded_patterns = [])

theorem detection_thm (app : WebApplication) (input : String) : detection_prop app input := by
  cases hs : detected scriptPatterns input <;>
    cases he : detected encodedPatterns input <;>
    simp [detection_prop, detect_xss_patterns, detectionFrom, hs, he]

/-- An independent branch-by-branch output specification. The substitutions
remain sequential: later keys can even replace placeholders in an earlier value.
In particular, universal substring preservation would be false for comment,
search and profile inputs containing such placeholders. -/
def expectedHTML (input : String) : String :=
  if containsText (routeLower input) "comment" then
    (commentTemplate.replace "{{comment_text}}" input).replace "{{username}}" "user123"
  else if containsText (routeLower input) "search" then
    (searchTemplate.replace "{{search_query}}" input).replace "{{result_count}}" "5"
  else if containsText (routeLower input) "profile" then
    ((profileTemplate.replace "{{display_name}}" input).replace "{{bio}}" "User bio").replace
      "{{location}}" "Unknown"
  else genericTemplate.replace "{{user_input}}" input

def expectedType (input : String) : String :=
  if containsText (routeLower input) "comment" then "comment_xss"
  else if containsText (routeLower input) "search" then "search_xss"
  else if containsText (routeLower input) "profile" then "profile_xss"
  else "generic_xss"

def handling_prop (app : WebApplication) (input : String) : Prop :=
  let r := unsafe_xss_handling app input
  r.type = expectedType input ∧ r.rendered_html = expectedHTML input ∧
  r.xss_detection = detect_xss_patterns app input ∧ r.vulnerable = true

theorem handling_thm (app : WebApplication) (input : String) : handling_prop app input := by
  unfold handling_prop unsafe_xss_handling scenario expectedType expectedHTML
  split <;> (try split) <;> (try split) <;>
    simp [Scenario.typeName, Scenario.template, Scenario.context, render_template,
      substitute, placeholder, List.foldl]

/-- Both state preservation and independence from any pre-existing state. -/
def state_prop (app other : WebApplication) (input : String) : Prop :=
  (handleState app input).2 = app ∧
  unsafe_xss_handling app input = unsafe_xss_handling other input

theorem state_thm (app other : WebApplication) (input : String) : state_prop app other input := by
  exact ⟨rfl, rfl⟩

/-- Membership is an exact existential regex-search specification, not just a
one-way alarm implication. Function-valued regexes need no equality decision. -/
theorem detected_mem_iff (patterns : List (String × Regex)) (input name : String) :
    name ∈ detected patterns input ↔
    ∃ r, (name, r) ∈ patterns ∧ regexSearch r input = true := by
  simp only [detected, List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨⟨n, r⟩, ⟨hm, hr⟩, hn⟩
    dsimp at hn
    subst n
    exact ⟨r, hm, hr⟩
  · rintro ⟨r, hm, hr⟩
    exact ⟨(name, r), ⟨hm, hr⟩, rfl⟩

/-- Each regex search succeeds exactly when some suffix admits all its pieces.
The empty final regex imposes no end anchor, as with Python re.search. -/
def PrefixMatch : Regex → List Char → Prop
  | [], _ => True
  | p :: ps, input => ∃ rest ∈ consume p input, PrefixMatch ps rest

theorem matchesHere_iff (r : Regex) (input : List Char) :
    matchesHere r input = true ↔ PrefixMatch r input := by
  induction r generalizing input with
  | nil => simp [matchesHere, PrefixMatch]
  | cons p ps ih => simp [matchesHere, PrefixMatch, List.any_eq_true, ih]

def SuffixMatch (r : Regex) (input : List Char) : Prop :=
  ∃ before rest, input = before ++ rest ∧ PrefixMatch r rest

theorem searchChars_iff (r : Regex) (input : List Char) :
    searchChars r input = true ↔ SuffixMatch r input := by
  induction input with
  | nil => simp [searchChars, matchesHere_iff, SuffixMatch]
  | cons c cs ih =>
    rw [searchChars, Bool.or_eq_true, matchesHere_iff, ih]
    constructor
    · rintro (h | ⟨before, rest, heq, hm⟩)
      · exact ⟨[], c :: cs, rfl, h⟩
      · exact ⟨c :: before, rest, by simp [heq], hm⟩
    · rintro ⟨before, rest, heq, hm⟩
      cases before with
      | nil => exact Or.inl (by simpa using heq ▸ hm)
      | cons b bs =>
        have htail : cs = bs ++ rest := (List.cons.inj heq).2
        exact Or.inr ⟨bs, rest, htail, hm⟩

/-- Repetition enumerates exactly the suffixes obtained by consuming a prefix
whose characters all satisfy the class, including the empty prefix. -/
theorem runEnds_iff (p : Char → Bool) (input rest : List Char) :
    rest ∈ runEnds p input ↔ ∃ pre, input = pre ++ rest ∧ pre.all p = true := by
  induction input generalizing rest with
  | nil =>
    constructor
    · intro h
      have hr : rest = [] := List.mem_singleton.mp h
      subst rest
      exact ⟨[], rfl, rfl⟩
    · rintro ⟨pre, heq, _⟩
      have hr : rest = [] := (List.append_eq_nil_iff.mp heq.symm).2
      subst rest
      exact List.mem_cons_self
  | cons c cs ih =>
    constructor
    · intro h
      rcases List.mem_cons.mp h with heq | hm
      · exact ⟨[], heq.symm, rfl⟩
      · by_cases hp : p c = true
        · have hm' : rest ∈ runEnds p cs := by simpa [hp] using hm
          obtain ⟨pre, heq, hall⟩ := (ih rest).mp hm'
          exact ⟨c :: pre, by simp [heq], by simp [hp, hall]⟩
        · simp [hp] at hm
    · rintro ⟨pre, heq, hall⟩
      cases pre with
      | nil =>
        have hr : c :: cs = rest := by simpa using heq
        subst rest
        exact List.mem_cons_self
      | cons d ds =>
        have hc : c = d := (List.cons.inj heq).1
        have ht : cs = ds ++ rest := (List.cons.inj heq).2
        subst d
        have hh : p c = true ∧ ds.all p = true := by simpa using hall
        have hm : rest ∈ runEnds p cs := (ih rest).mpr ⟨ds, ht, hh.2⟩
        change rest ∈ (c :: cs) :: (if p c then runEnds p cs else [])
        rw [if_pos hh.1]
        exact List.mem_cons_of_mem _ hm

/-- Exact semantic membership for each reported regex label. The recognizer
accepts a pattern iff it matches a prefix of some input suffix. -/
def recognition_prop (app : WebApplication) (input : String) : Prop :=
  (∀ name, name ∈ (detect_xss_patterns app input).script_patterns ↔
    ∃ r, (name, r) ∈ scriptPatterns ∧ SuffixMatch r input.toList) ∧
  (∀ name, name ∈ (detect_xss_patterns app input).encoded_patterns ↔
    ∃ r, (name, r) ∈ encodedPatterns ∧ SuffixMatch r input.toList)

theorem recognition_thm (app : WebApplication) (input : String) : recognition_prop app input := by
  simp only [recognition_prop, detect_xss_patterns, detectionFrom, detected_mem_iff,
    regexSearch, searchChars_iff, and_self]
  exact fun _ => True.intro

/-- All application obligations; the renderer obligations quantify over the
selected template/context and over all subsequent context entries. -/
def Post_prop (app : WebApplication) (input : String) : Prop :=
  handling_prop app input ∧ detection_prop app input ∧ recognition_prop app input ∧ escape_prop input ∧
  (∀ other, state_prop app other input) ∧
  (∀ later, rendering_prop app (scenario input).template ((scenario input).context input) later)

/-! ## Bounded property-based tests

The corpus crosses payloads with all routing prefixes and boundary suffixes.
Each named executable property, and their postcondition, is checked separately.
These tests are evidence only; none is used in a theorem proof.
-/

def payloads : List String := inputs ++
  ["", "ordinary", "{{username}}", "{{bio}}", "{{result_count}}", "&<>\"'",
   "<script>\n</script>", "<script a='>'>ok</script>", "<scriptx>x</script>",
   "<iframe", "<OBJECT>", "<EMBED/>", "<form>", "<input>", "<textarea>",
   "<select>", "<link>", "<meta>", "<svg>", "<p oné\t=", "<span onx=",
   "<div onload =", "<img onx=", "<a href = 'JaVaScRiPt:",
   "on=", "onx=", "on中\u00a0=", "on_ =", "JAVASCRİPT:", "javaſcript:",
   "&#123;", "&#FACE;", "&#xdead;", "&#X12;", "%12", "%1G", "\\xAB", "\\XAB",
   "\\u1234", "\\U1234", "COMMENT SEARCH PROFILE", "PROFİLE"]

def corpus : List String :=
  ["", "comment ", "search ", "profile ", "search COMMENT ", "PROFILE SEARCH "].flatMap
    fun pre => payloads.flatMap fun s => [pre ++ s, pre ++ s ++ "\n>"]

def appStates : List WebApplication :=
  [testApp, ⟨[("u", "session")], ["old comment"], ["old search"]⟩]

def contexts : List Context :=
  [[], [("x", "<script>")], [("x", "{{y}}"), ("y", "<&'\"")],
   [("comment_text", "{{username}}"), ("username", "user123")]]

def renderingCheck (app : WebApplication) (t : String) (c d : Context) : Bool :=
  render_template app t (c ++ d) == render_template app (render_template app t c) d &&
  safe_render_template app t c == render_template app t (escapeContext c)

def escapeCheck (s : String) : Bool :=
  ['<', '>', '"', '\''].all fun c => !(htmlEscape s).toList.contains c

def detectionCheck (app : WebApplication) (s : String) : Bool :=
  let d := detect_xss_patterns app s
  d.script_patterns == detected scriptPatterns s &&
  d.encoded_patterns == detected encodedPatterns s &&
  (d.xss_detected == (!d.script_patterns.isEmpty || !d.encoded_patterns.isEmpty)) &&
  ((d.risk_level == .HIGH) == !d.script_patterns.isEmpty) &&
  ((d.risk_level == .MEDIUM) == (d.script_patterns.isEmpty && !d.encoded_patterns.isEmpty)) &&
  ((d.risk_level == .LOW) == (d.script_patterns.isEmpty && d.encoded_patterns.isEmpty))

def handlingCheck (app : WebApplication) (s : String) : Bool :=
  let r := unsafe_xss_handling app s
  r.type == expectedType s && r.rendered_html == expectedHTML s &&
  r.xss_detection == detect_xss_patterns app s && r.vulnerable

def stateCheck (app other : WebApplication) (s : String) : Bool :=
  (handleState app s).2 == app && unsafe_xss_handling app s == unsafe_xss_handling other s

/-- Executable form of recognition_prop, using searchChars_iff to reflect
SuffixMatch. Test all declared names as well as unrelated payload strings. -/
def recognitionCheck (app : WebApplication) (s : String) : Bool :=
  let d := detect_xss_patterns app s
  let names := (scriptPatterns ++ encodedPatterns).map Prod.fst ++ payloads
  names.all fun name =>
    (d.script_patterns.contains name == scriptPatterns.any (fun p => p.1 == name && regexSearch p.2 s)) &&
    (d.encoded_patterns.contains name == encodedPatterns.any (fun p => p.1 == name && regexSearch p.2 s))

def postCheck (app : WebApplication) (s : String) : Bool :=
  handlingCheck app s && detectionCheck app s && recognitionCheck app s && escapeCheck s &&
  appStates.all (fun other => stateCheck app other s) &&
  contexts.all (fun later => renderingCheck app (scenario s).template ((scenario s).context s) later)

-- PBT: rendering_prop (also exercises contexts independently of routing).
example : (["{{x}} {{y}}", "{{{x}}}", commentTemplate, ""].all fun t =>
    contexts.all fun c => contexts.all fun d => renderingCheck testApp t c d) = true := by native_decide
-- PBT: escape_prop.
example : corpus.all escapeCheck = true := by native_decide
-- PBT: detection_prop.
example : corpus.all (detectionCheck testApp) = true := by native_decide
/-- A separate finite enumeration of possible repetition lengths. -/
def referenceEnds (p : Char → Bool) (cs : List Char) : List (List Char) :=
  (List.range (cs.length + 1)).filterMap fun n =>
    if (cs.take n).all p then some (cs.drop n) else none

-- PBT: runEnds_iff, including zero-length and Unicode-class runs.
example : (payloads.all fun s =>
    ([wordChar, spaceChar, fun c => c != '>', fun c => c != '\n'].all fun p =>
      runEnds p s.toList == referenceEnds p s.toList)) = true := by native_decide

-- PBT: recognition_prop (exact membership, including negative names).
example : corpus.all (recognitionCheck testApp) = true := by native_decide
-- PBT: handling_prop.
example : corpus.all (handlingCheck testApp) = true := by native_decide
-- PBT: state_prop.
example : (appStates.all fun a => appStates.all fun b => corpus.all (stateCheck a b)) = true := by native_decide
-- PBT: Post_prop; universally quantified state/context clauses are bounded above.
example : (appStates.all fun app => corpus.all (postCheck app)) = true := by native_decide
#eval (corpus.length, corpus.all (postCheck testApp))

/-- Independent regression oracle produced by the public Python regexes and
`html.escape` (Unicode 15.0), with deterministic seed 82026. Each tuple records
input, complete detection dictionary, escaped input, and branch type. -/
def pythonOracle : List (String × Detection × String × String) :=
  [("", ⟨false, [], [], .LOW⟩, "", "generic_xss"),
   ("plain text", ⟨false, [], [], .LOW⟩, "plain text", "generic_xss"),
   ("<script>a</script>", ⟨true, ["<script[^>]*>.*?</script>"], [], .HIGH⟩, "&lt;script&gt;a&lt;/script&gt;", "generic_xss"),
   ("<SCRIPT a=\"x\">test</script>", ⟨true, ["<script[^>]*>.*?</script>"], [], .HIGH⟩, "&lt;SCRIPT a=&quot;x&quot;&gt;test&lt;/script&gt;", "generic_xss"),
   ("<script>\n</script>", ⟨false, [], [], .LOW⟩, "&lt;script&gt;\n&lt;/script&gt;", "generic_xss"),
   ("<script>\r</script>", ⟨true, ["<script[^>]*>.*?</script>"], [], .HIGH⟩, "&lt;script&gt;\r&lt;/script&gt;", "generic_xss"),
   ("<script> </script>", ⟨true, ["<script[^>]*>.*?</script>"], [], .HIGH⟩, "&lt;script&gt; &lt;/script&gt;", "generic_xss"),
   ("<ſcrİpt>x</scrıpt>", ⟨true, ["<script[^>]*>.*?</script>"], [], .HIGH⟩, "&lt;ſcrİpt&gt;x&lt;/scrıpt&gt;", "generic_xss"),
   ("JaVaScRiPt:", ⟨true, ["javascript:"], [], .HIGH⟩, "JaVaScRiPt:", "generic_xss"),
   ("on =", ⟨false, [], [], .LOW⟩, "on =", "generic_xss"),
   ("onx=", ⟨true, ["on\\w+\\s*="], [], .HIGH⟩, "onx=", "generic_xss"),
   ("oné =", ⟨true, ["on\\w+\\s*="], [], .HIGH⟩, "oné =", "generic_xss"),
   ("on中 =", ⟨true, ["on\\w+\\s*="], [], .HIGH⟩, "on中 =", "generic_xss"),
   ("oń=", ⟨false, [], [], .LOW⟩, "oń=", "generic_xss"),
   ("on_ =", ⟨true, ["on\\w+\\s*="], [], .HIGH⟩, "on_ =", "generic_xss"),
   ("on²=", ⟨true, ["on\\w+\\s*="], [], .HIGH⟩, "on²=", "generic_xss"),
   ("on\u001c=", ⟨false, [], [], .LOW⟩, "on\u001c=", "generic_xss"),
   ("<a href=\"javascript:", ⟨true, ["javascript:", "<a[^>]*href\\s*=\\s*[\"\\']javascript:"], [], .HIGH⟩, "&lt;a href=&quot;javascript:", "generic_xss"),
   ("<a href = 'javaſcript:", ⟨true, ["javascript:", "<a[^>]*href\\s*=\\s*[\"\\']javascript:"], [], .HIGH⟩, "&lt;a href = &#x27;javaſcript:", "generic_xss"),
   ("<a href=javascript:", ⟨true, ["javascript:"], [], .HIGH⟩, "&lt;a href=javascript:", "generic_xss"),
   ("<div x >onload=", ⟨true, ["on\\w+\\s*="], [], .HIGH⟩, "&lt;div x &gt;onload=", "generic_xss"),
   ("<img > onerror=", ⟨true, ["on\\w+\\s*="], [], .HIGH⟩, "&lt;img &gt; onerror=", "generic_xss"),
   ("&#FACE;", ⟨true, [], ["&#x?[0-9a-fA-F]+;"], .MEDIUM⟩, "&amp;#FACE;", "generic_xss"),
   ("&#xabc;", ⟨true, [], ["&#x?[0-9a-fA-F]+;"], .MEDIUM⟩, "&amp;#xabc;", "generic_xss"),
   ("&#Xabc;", ⟨false, [], [], .LOW⟩, "&amp;#Xabc;", "generic_xss"),
   ("&#;", ⟨false, [], [], .LOW⟩, "&amp;#;", "generic_xss"),
   ("&#x;", ⟨false, [], [], .LOW⟩, "&amp;#x;", "generic_xss"),
   ("%00", ⟨true, [], ["%[0-9a-fA-F]{2}"], .MEDIUM⟩, "%00", "generic_xss"),
   ("%fg", ⟨false, [], [], .LOW⟩, "%fg", "generic_xss"),
   ("\\xFE", ⟨true, [], ["\\\\x[0-9a-fA-F]{2}"], .MEDIUM⟩, "\\xFE", "generic_xss"),
   ("\\XFE", ⟨false, [], [], .LOW⟩, "\\XFE", "generic_xss"),
   ("\\u1234", ⟨true, [], ["\\\\u[0-9a-fA-F]{4}"], .MEDIUM⟩, "\\u1234", "generic_xss"),
   ("\\u123", ⟨false, [], [], .LOW⟩, "\\u123", "generic_xss"),
   ("\\U1234", ⟨false, [], [], .LOW⟩, "\\U1234", "generic_xss"),
   ("<&\"'>&", ⟨false, [], [], .LOW⟩, "&lt;&amp;&quot;&#x27;&gt;&amp;", "generic_xss"),
   ("PROFİLE", ⟨false, [], [], .LOW⟩, "PROFİLE", "generic_xss"),
   ("profile", ⟨false, [], [], .LOW⟩, "profile", "profile_xss"),
   ("COMMENT SEARCH PROFILE", ⟨false, [], [], .LOW⟩, "COMMENT SEARCH PROFILE", "comment_xss"),
   ("{{username}}", ⟨false, [], [], .LOW⟩, "{{username}}", "generic_xss"),
   ("{{bio}}", ⟨false, [], [], .LOW⟩, "{{bio}}", "generic_xss"),
   ("<iframe>", ⟨true, ["<iframe[^>]*>"], [], .HIGH⟩, "&lt;iframe&gt;", "generic_xss"),
   ("<IFRAMEsuffix\n attr=1>", ⟨true, ["<iframe[^>]*>"], [], .HIGH⟩, "&lt;IFRAMEsuffix\n attr=1&gt;", "generic_xss"),
   ("<iframe", ⟨false, [], [], .LOW⟩, "&lt;iframe", "generic_xss"),
   ("<iframe >", ⟨true, ["<iframe[^>]*>"], [], .HIGH⟩, "&lt;iframe &gt;", "generic_xss"),
   ("<object>", ⟨true, ["<object[^>]*>"], [], .HIGH⟩, "&lt;object&gt;", "generic_xss"),
   ("<OBJECTsuffix\n attr=1>", ⟨true, ["<object[^>]*>"], [], .HIGH⟩, "&lt;OBJECTsuffix\n attr=1&gt;", "generic_xss"),
   ("<object", ⟨false, [], [], .LOW⟩, "&lt;object", "generic_xss"),
   ("<object >", ⟨true, ["<object[^>]*>"], [], .HIGH⟩, "&lt;object &gt;", "generic_xss"),
   ("<embed>", ⟨true, ["<embed[^>]*>"], [], .HIGH⟩, "&lt;embed&gt;", "generic_xss"),
   ("<EMBEDsuffix\n attr=1>", ⟨true, ["<embed[^>]*>"], [], .HIGH⟩, "&lt;EMBEDsuffix\n attr=1&gt;", "generic_xss"),
   ("<embed", ⟨false, [], [], .LOW⟩, "&lt;embed", "generic_xss"),
   ("<embed >", ⟨true, ["<embed[^>]*>"], [], .HIGH⟩, "&lt;embed &gt;", "generic_xss"),
   ("<form>", ⟨true, ["<form[^>]*>"], [], .HIGH⟩, "&lt;form&gt;", "generic_xss"),
   ("<FORMsuffix\n attr=1>", ⟨true, ["<form[^>]*>"], [], .HIGH⟩, "&lt;FORMsuffix\n attr=1&gt;", "generic_xss"),
   ("<form", ⟨false, [], [], .LOW⟩, "&lt;form", "generic_xss"),
   ("<form >", ⟨true, ["<form[^>]*>"], [], .HIGH⟩, "&lt;form &gt;", "generic_xss"),
   ("<input>", ⟨true, ["<input[^>]*>"], [], .HIGH⟩, "&lt;input&gt;", "generic_xss"),
   ("<INPUTsuffix\n attr=1>", ⟨true, ["<input[^>]*>"], [], .HIGH⟩, "&lt;INPUTsuffix\n attr=1&gt;", "generic_xss"),
   ("<input", ⟨false, [], [], .LOW⟩, "&lt;input", "generic_xss"),
   ("<input >", ⟨true, ["<input[^>]*>"], [], .HIGH⟩, "&lt;input &gt;", "generic_xss"),
   ("<textarea>", ⟨true, ["<textarea[^>]*>"], [], .HIGH⟩, "&lt;textarea&gt;", "generic_xss"),
   ("<TEXTAREAsuffix\n attr=1>", ⟨true, ["<textarea[^>]*>"], [], .HIGH⟩, "&lt;TEXTAREAsuffix\n attr=1&gt;", "generic_xss"),
   ("<textarea", ⟨false, [], [], .LOW⟩, "&lt;textarea", "generic_xss"),
   ("<textarea >", ⟨true, ["<textarea[^>]*>"], [], .HIGH⟩, "&lt;textarea &gt;", "generic_xss"),
   ("<select>", ⟨true, ["<select[^>]*>"], [], .HIGH⟩, "&lt;select&gt;", "generic_xss"),
   ("<SELECTsuffix\n attr=1>", ⟨true, ["<select[^>]*>"], [], .HIGH⟩, "&lt;SELECTsuffix\n attr=1&gt;", "generic_xss"),
   ("<select", ⟨false, [], [], .LOW⟩, "&lt;select", "generic_xss"),
   ("<select >", ⟨true, ["<select[^>]*>"], [], .HIGH⟩, "&lt;select &gt;", "generic_xss"),
   ("<link>", ⟨true, ["<link[^>]*>"], [], .HIGH⟩, "&lt;link&gt;", "generic_xss"),
   ("<LINKsuffix\n attr=1>", ⟨true, ["<link[^>]*>"], [], .HIGH⟩, "&lt;LINKsuffix\n attr=1&gt;", "generic_xss"),
   ("<link", ⟨false, [], [], .LOW⟩, "&lt;link", "generic_xss"),
   ("<link >", ⟨true, ["<link[^>]*>"], [], .HIGH⟩, "&lt;link &gt;", "generic_xss"),
   ("<meta>", ⟨true, ["<meta[^>]*>"], [], .HIGH⟩, "&lt;meta&gt;", "generic_xss"),
   ("<METAsuffix\n attr=1>", ⟨true, ["<meta[^>]*>"], [], .HIGH⟩, "&lt;METAsuffix\n attr=1&gt;", "generic_xss"),
   ("<meta", ⟨false, [], [], .LOW⟩, "&lt;meta", "generic_xss"),
   ("<meta >", ⟨true, ["<meta[^>]*>"], [], .HIGH⟩, "&lt;meta &gt;", "generic_xss"),
   ("<style>", ⟨true, ["<style[^>]*>"], [], .HIGH⟩, "&lt;style&gt;", "generic_xss"),
   ("<STYLEsuffix\n attr=1>", ⟨true, ["<style[^>]*>"], [], .HIGH⟩, "&lt;STYLEsuffix\n attr=1&gt;", "generic_xss"),
   ("<style", ⟨false, [], [], .LOW⟩, "&lt;style", "generic_xss"),
   ("<style >", ⟨true, ["<style[^>]*>"], [], .HIGH⟩, "&lt;style &gt;", "generic_xss"),
   ("<svg>", ⟨true, ["<svg[^>]*>"], [], .HIGH⟩, "&lt;svg&gt;", "generic_xss"),
   ("<SVGsuffix\n attr=1>", ⟨true, ["<svg[^>]*>"], [], .HIGH⟩, "&lt;SVGsuffix\n attr=1&gt;", "generic_xss"),
   ("<svg", ⟨false, [], [], .LOW⟩, "&lt;svg", "generic_xss"),
   ("<svg >", ⟨true, ["<svg[^>]*>"], [], .HIGH⟩, "&lt;svg &gt;", "generic_xss"),
   ("<img onclick =", ⟨true, ["on\\w+\\s*=", "<img[^>]*on\\w+\\s*="], [], .HIGH⟩, "&lt;img onclick =", "generic_xss"),
   ("<IMG ON中\t=", ⟨true, ["on\\w+\\s*=", "<img[^>]*on\\w+\\s*="], [], .HIGH⟩, "&lt;IMG ON中\t=", "generic_xss"),
   ("<img>onerror=", ⟨true, ["on\\w+\\s*="], [], .HIGH⟩, "&lt;img&gt;onerror=", "generic_xss"),
   ("<imgonx=", ⟨true, ["on\\w+\\s*=", "<img[^>]*on\\w+\\s*="], [], .HIGH⟩, "&lt;imgonx=", "generic_xss"),
   ("<div onclick =", ⟨true, ["on\\w+\\s*=", "<div[^>]*on\\w+\\s*="], [], .HIGH⟩, "&lt;div onclick =", "generic_xss"),
   ("<DIV ON中\t=", ⟨true, ["on\\w+\\s*=", "<div[^>]*on\\w+\\s*="], [], .HIGH⟩, "&lt;DIV ON中\t=", "generic_xss"),
   ("<div>onerror=", ⟨true, ["on\\w+\\s*="], [], .HIGH⟩, "&lt;div&gt;onerror=", "generic_xss"),
   ("<divonx=", ⟨true, ["on\\w+\\s*=", "<div[^>]*on\\w+\\s*="], [], .HIGH⟩, "&lt;divonx=", "generic_xss"),
   ("<span onclick =", ⟨true, ["on\\w+\\s*=", "<span[^>]*on\\w+\\s*="], [], .HIGH⟩, "&lt;span onclick =", "generic_xss"),
   ("<SPAN ON中\t=", ⟨true, ["on\\w+\\s*=", "<span[^>]*on\\w+\\s*="], [], .HIGH⟩, "&lt;SPAN ON中\t=", "generic_xss"),
   ("<span>onerror=", ⟨true, ["on\\w+\\s*="], [], .HIGH⟩, "&lt;span&gt;onerror=", "generic_xss"),
   ("<spanonx=", ⟨true, ["on\\w+\\s*=", "<span[^>]*on\\w+\\s*="], [], .HIGH⟩, "&lt;spanonx=", "generic_xss"),
   ("<p onclick =", ⟨true, ["on\\w+\\s*=", "<p[^>]*on\\w+\\s*="], [], .HIGH⟩, "&lt;p onclick =", "generic_xss"),
   ("<P ON中\t=", ⟨true, ["on\\w+\\s*=", "<p[^>]*on\\w+\\s*="], [], .HIGH⟩, "&lt;P ON中\t=", "generic_xss"),
   ("<p>onerror=", ⟨true, ["on\\w+\\s*="], [], .HIGH⟩, "&lt;p&gt;onerror=", "generic_xss"),
   ("<ponx=", ⟨true, ["on\\w+\\s*=", "<p[^>]*on\\w+\\s*="], [], .HIGH⟩, "&lt;ponx=", "generic_xss"),
   ("\t<oncomment</script>", ⟨false, [], [], .LOW⟩, "\t&lt;oncomment&lt;/script&gt;", "comment_xss"),
   ("</script>\\uscript", ⟨false, [], [], .LOW⟩, "&lt;/script&gt;\\uscript", "generic_xss"),
   ("AF12SEARCH\\x %\\u\t\n", ⟨false, [], [], .LOW⟩, "AF12SEARCH\\x %\\u\t\n", "search_xss"),
   ("\nscriptAF\\xoncomment\\u12é", ⟨false, [], [], .LOW⟩, "\nscriptAF\\xoncomment\\u12é", "comment_xss"),
   ("é%\\x  中=&#%\n", ⟨false, [], [], .LOW⟩, "é%\\x  中=&amp;#%\n", "generic_xss"),
   ("中<\t\\uon'comment\"scriptjavascript:", ⟨true, ["javascript:"], [], .HIGH⟩, "中&lt;\t\\uon&#x27;comment&quot;scriptjavascript:", "comment_xss"),
   ("javascript:;'javascript:\\u&#", ⟨true, ["javascript:"], [], .HIGH⟩, "javascript:;&#x27;javascript:\\u&amp;#", "generic_xss"),
   ("\\u'x\t>error 中&#script", ⟨false, [], [], .LOW⟩, "\\u&#x27;x\t&gt;error 中&amp;#script", "generic_xss"),
   ("SEARCH\t</script>é", ⟨false, [], [], .LOW⟩, "SEARCH\t&lt;/script&gt;é", "search_xss"),
   ("error\\u\\x", ⟨false, [], [], .LOW⟩, "error\\u\\x", "generic_xss"),
   ("script", ⟨false, [], [], .LOW⟩, "script", "generic_xss"),
   ("\\ux&#\\u12onx中\"", ⟨false, [], [], .LOW⟩, "\\ux&amp;#\\u12onx中&quot;", "generic_xss"),
   ("errorjavascript:SEARCHjavascript:</script>>%=12comment\t", ⟨true, ["javascript:"], [], .HIGH⟩, "errorjavascript:SEARCHjavascript:&lt;/script&gt;&gt;%=12comment\t", "comment_xss"),
   ("%", ⟨false, [], [], .LOW⟩, "%", "generic_xss"),
   ("script&#;onx\\ux\t", ⟨false, [], [], .LOW⟩, "script&amp;#;onx\\ux\t", "generic_xss"),
   ("\\u</script>AF=</script>\\x</script>中\\x\\u", ⟨false, [], [], .LOW⟩, "\\u&lt;/script&gt;AF=&lt;/script&gt;\\x&lt;/script&gt;中\\x\\u", "generic_xss"),
   ("</script>\"</script></script>x\"", ⟨false, [], [], .LOW⟩, "&lt;/script&gt;&quot;&lt;/script&gt;&lt;/script&gt;x&quot;", "generic_xss"),
   ("\"", ⟨false, [], [], .LOW⟩, "&quot;", "generic_xss"),
   ("é", ⟨false, [], [], .LOW⟩, "é", "generic_xss"),
   ("é\\u%", ⟨false, [], [], .LOW⟩, "é\\u%", "generic_xss"),
   ("\"=script%AF=\\uAF\n", ⟨true, [], ["%[0-9a-fA-F]{2}"], .MEDIUM⟩, "&quot;=script%AF=\\uAF\n", "generic_xss"),
   ("&#javascript:<é", ⟨true, ["javascript:"], [], .HIGH⟩, "&amp;#javascript:&lt;é", "generic_xss"),
   ("'=x'<\\ux1212SEARCH", ⟨false, [], [], .LOW⟩, "&#x27;=x&#x27;&lt;\\ux1212SEARCH", "search_xss"),
   (" x", ⟨false, [], [], .LOW⟩, " x", "generic_xss"),
   ("&#<javascript:scripton", ⟨true, ["javascript:"], [], .HIGH⟩, "&amp;#&lt;javascript:scripton", "generic_xss"),
   ("12\\xAFscript", ⟨true, [], ["\\\\x[0-9a-fA-F]{2}"], .MEDIUM⟩, "12\\xAFscript", "generic_xss"),
   ("javascript:\"javascript:中\\uonAF\tAF=script", ⟨true, ["javascript:"], [], .HIGH⟩, "javascript:&quot;javascript:中\\uonAF\tAF=script", "generic_xss"),
   ("\ton\t12AF<;SEARCH", ⟨false, [], [], .LOW⟩, "\ton\t12AF&lt;;SEARCH", "search_xss"),
   ("&#</script>\\u=12>javascript:中<on", ⟨true, ["javascript:"], [], .HIGH⟩, "&amp;#&lt;/script&gt;\\u=12&gt;javascript:中&lt;on", "generic_xss"),
   ("\"12x<x12\\u\t;%", ⟨false, [], [], .LOW⟩, "&quot;12x&lt;x12\\u\t;%", "generic_xss"),
   ("'javascript:commenton on\\u\\x';", ⟨true, ["javascript:"], [], .HIGH⟩, "&#x27;javascript:commenton on\\u\\x&#x27;;", "comment_xss"),
   ("&#中&# 12javascript:'AF>", ⟨true, ["javascript:"], [], .HIGH⟩, "&amp;#中&amp;# 12javascript:&#x27;AF&gt;", "generic_xss"),
   (";onon<%script \nAF", ⟨false, [], [], .LOW⟩, ";onon&lt;%script \nAF", "generic_xss"),
   ("\t=SEARCH12&#\"", ⟨false, [], [], .LOW⟩, "\t=SEARCH12&amp;#&quot;", "search_xss"),
   (" ;12</script>'<", ⟨false, [], [], .LOW⟩, " ;12&lt;/script&gt;&#x27;&lt;", "generic_xss"),
   ("&#", ⟨false, [], [], .LOW⟩, "&amp;#", "generic_xss"),
   ("中中=</script>>&#script", ⟨false, [], [], .LOW⟩, "中中=&lt;/script&gt;&gt;&amp;#script", "generic_xss"),
   ("12oné\\u\\xcommentSEARCHcomment\\xscript", ⟨false, [], [], .LOW⟩, "12oné\\u\\xcommentSEARCHcomment\\xscript", "comment_xss"),
   ("%SEARCH\t>éerror", ⟨false, [], [], .LOW⟩, "%SEARCH\t&gt;éerror", "search_xss"),
   ("javascript:&#=\n'javascript:<\t'\\u", ⟨true, ["javascript:"], [], .HIGH⟩, "javascript:&amp;#=\n&#x27;javascript:&lt;\t&#x27;\\u", "generic_xss"),
   ("\t;AF=AFx中", ⟨false, [], [], .LOW⟩, "\t;AF=AFx中", "generic_xss"),
   ("\t'12;é", ⟨false, [], [], .LOW⟩, "\t&#x27;12;é", "generic_xss"),
   ("%javascript:12'é%on%", ⟨true, ["javascript:"], [], .HIGH⟩, "%javascript:12&#x27;é%on%", "generic_xss"),
   ("scripterrorscript\nonéerror12</script>é", ⟨false, [], [], .LOW⟩, "scripterrorscript\nonéerror12&lt;/script&gt;é", "generic_xss"),
   ("script=%scriptscript</script>;>éé", ⟨false, [], [], .LOW⟩, "script=%scriptscript&lt;/script&gt;;&gt;éé", "generic_xss"),
   ("&#x\\u\"</script>", ⟨false, [], [], .LOW⟩, "&amp;#x\\u&quot;&lt;/script&gt;", "generic_xss"),
   ("script'\n\"中</script>", ⟨false, [], [], .LOW⟩, "script&#x27;\n&quot;中&lt;/script&gt;", "generic_xss"),
   ("javascript:\n'AFcomment%\\xjavascript:中", ⟨true, ["javascript:"], [], .HIGH⟩, "javascript:\n&#x27;AFcomment%\\xjavascript:中", "comment_xss"),
   (">12javascript:'<comment\\x中\nscriptjavascript:", ⟨true, ["javascript:"], [], .HIGH⟩, "&gt;12javascript:&#x27;&lt;comment\\x中\nscriptjavascript:", "comment_xss"),
   ("=javascript:script</script><é%x>script", ⟨true, ["javascript:"], [], .HIGH⟩, "=javascript:script&lt;/script&gt;&lt;é%x&gt;script", "generic_xss"),
   ("12", ⟨false, [], [], .LOW⟩, "12", "generic_xss"),
   ("SEARCH'javascript:é\nx%%", ⟨true, ["javascript:"], [], .HIGH⟩, "SEARCH&#x27;javascript:é\nx%%", "search_xss"),
   ("scriptxx>errorx12%xjavascript:", ⟨true, ["javascript:"], [], .HIGH⟩, "scriptxx&gt;errorx12%xjavascript:", "generic_xss"),
   (";>\\u>comment</script>;javascript:=\\u", ⟨true, ["javascript:"], [], .HIGH⟩, ";&gt;\\u&gt;comment&lt;/script&gt;;javascript:=\\u", "comment_xss"),
   ("中<%;'\\x</script>=x", ⟨false, [], [], .LOW⟩, "中&lt;%;&#x27;\\x&lt;/script&gt;=x", "generic_xss"),
   ("=\"", ⟨false, [], [], .LOW⟩, "=&quot;", "generic_xss"),
   ("x><comment中\"&#comment\"\ton", ⟨false, [], [], .LOW⟩, "x&gt;&lt;comment中&quot;&amp;#comment&quot;\ton", "comment_xss"),
   (" SEARCH\n", ⟨false, [], [], .LOW⟩, " SEARCH\n", "search_xss"),
   ("<", ⟨false, [], [], .LOW⟩, "&lt;", "generic_xss"),
   ("&#12x12SEARCH中12=\t =", ⟨false, [], [], .LOW⟩, "&amp;#12x12SEARCH中12=\t =", "search_xss"),
   ("\"\\xcommentscript中\"comment中&#x", ⟨false, [], [], .LOW⟩, "&quot;\\xcommentscript中&quot;comment中&amp;#x", "comment_xss"),
   ("</script>SEARCHcomment", ⟨false, [], [], .LOW⟩, "&lt;/script&gt;SEARCHcomment", "comment_xss"),
   ("\\x</script>%é", ⟨false, [], [], .LOW⟩, "\\x&lt;/script&gt;%é", "generic_xss"),
   ("AF </script></script>\"中x", ⟨false, [], [], .LOW⟩, "AF &lt;/script&gt;&lt;/script&gt;&quot;中x", "generic_xss"),
   (";12\\x AF中", ⟨false, [], [], .LOW⟩, ";12\\x AF中", "generic_xss"),
   ("</script>&#é", ⟨false, [], [], .LOW⟩, "&lt;/script&gt;&amp;#é", "generic_xss"),
   ("\\x12%;'%", ⟨true, [], ["\\\\x[0-9a-fA-F]{2}"], .MEDIUM⟩, "\\x12%;&#x27;%", "generic_xss"),
   ("</script>script</script>12", ⟨false, [], [], .LOW⟩, "&lt;/script&gt;script&lt;/script&gt;12", "generic_xss"),
   ("SEARCH><>x% 中javascript:", ⟨true, ["javascript:"], [], .HIGH⟩, "SEARCH&gt;&lt;&gt;x% 中javascript:", "search_xss"),
   (";% ", ⟨false, [], [], .LOW⟩, ";% ", "generic_xss"),
   ("on<<\\x;\t", ⟨false, [], [], .LOW⟩, "on&lt;&lt;\\x;\t", "generic_xss"),
   ("\\x\t\\ujavascript:12comment</script>commentcomment\"&#", ⟨true, ["javascript:"], [], .HIGH⟩, "\\x\t\\ujavascript:12comment&lt;/script&gt;commentcomment&quot;&amp;#", "comment_xss"),
   ("</script>", ⟨false, [], [], .LOW⟩, "&lt;/script&gt;", "generic_xss"),
   ("x\\u\"\\x comment&#", ⟨false, [], [], .LOW⟩, "x\\u&quot;\\x comment&amp;#", "comment_xss"),
   (";>commentAFAF&#AF \t</script>on", ⟨false, [], [], .LOW⟩, ";&gt;commentAFAF&amp;#AF \t&lt;/script&gt;on", "comment_xss"),
   ("\\u", ⟨false, [], [], .LOW⟩, "\\u", "generic_xss"),
   ("onSEARCH12javascript:\t", ⟨true, ["javascript:"], [], .HIGH⟩, "onSEARCH12javascript:\t", "search_xss"),
   ("x ", ⟨false, [], [], .LOW⟩, "x ", "generic_xss"),
   ("%'é中>", ⟨false, [], [], .LOW⟩, "%&#x27;é中&gt;", "generic_xss"),
   ("x%></script>%\tjavascript:;on", ⟨true, ["javascript:"], [], .HIGH⟩, "x%&gt;&lt;/script&gt;%\tjavascript:;on", "generic_xss"),
   ("oncomment\\x<\n中=\"SEARCH", ⟨false, [], [], .LOW⟩, "oncomment\\x&lt;\n中=&quot;SEARCH", "comment_xss"),
   (" \\x", ⟨false, [], [], .LOW⟩, " \\x", "generic_xss"),
   ("\\x%%x%x", ⟨false, [], [], .LOW⟩, "\\x%%x%x", "generic_xss"),
   ("x\né&#é'&#>\\u</script>12", ⟨false, [], [], .LOW⟩, "x\né&amp;#é&#x27;&amp;#&gt;\\u&lt;/script&gt;12", "generic_xss"),
   ("AF &#'12\\u12;'", ⟨false, [], [], .LOW⟩, "AF &amp;#&#x27;12\\u12;&#x27;", "generic_xss"),
   (";comment\\x", ⟨false, [], [], .LOW⟩, ";comment\\x", "comment_xss"),
   ("SEARCH", ⟨false, [], [], .LOW⟩, "SEARCH", "search_xss"),
   ("中% 中% script>script", ⟨false, [], [], .LOW⟩, "中% 中% script&gt;script", "generic_xss"),
   ("é>\nscript\\uSEARCH'< ", ⟨false, [], [], .LOW⟩, "é&gt;\nscript\\uSEARCH&#x27;&lt; ", "search_xss"),
   ("SEARCH</script>>errorscript\"</script>javascript:AF12", ⟨true, ["javascript:"], [], .HIGH⟩, "SEARCH&lt;/script&gt;&gt;errorscript&quot;&lt;/script&gt;javascript:AF12", "search_xss"),
   ("javascript:onxAF\n", ⟨true, ["javascript:"], [], .HIGH⟩, "javascript:onxAF\n", "generic_xss"),
   ("12;", ⟨false, [], [], .LOW⟩, "12;", "generic_xss"),
   ("' %\\uerror\tcomment", ⟨false, [], [], .LOW⟩, "&#x27; %\\uerror\tcomment", "comment_xss"),
   ("AF\n", ⟨false, [], [], .LOW⟩, "AF\n", "generic_xss"),
   ("</script>;%error", ⟨false, [], [], .LOW⟩, "&lt;/script&gt;;%error", "generic_xss"),
   ("1212&#", ⟨false, [], [], .LOW⟩, "1212&amp;#", "generic_xss"),
   ("%SEARCH'\n=javascript:script", ⟨true, ["javascript:"], [], .HIGH⟩, "%SEARCH&#x27;\n=javascript:script", "search_xss"),
   (";&#script\\x\t%", ⟨false, [], [], .LOW⟩, ";&amp;#script\\x\t%", "generic_xss"),
   ("=commentjavascript:", ⟨true, ["javascript:"], [], .HIGH⟩, "=commentjavascript:", "comment_xss"),
   ("'12SEARCHscript\t%script\tscript\n", ⟨false, [], [], .LOW⟩, "&#x27;12SEARCHscript\t%script\tscript\n", "search_xss"),
   ("\nscript中javascript:AFAFjavascript:\\x;\t<", ⟨true, ["javascript:"], [], .HIGH⟩, "\nscript中javascript:AFAFjavascript:\\x;\t&lt;", "generic_xss"),
   ("on", ⟨false, [], [], .LOW⟩, "on", "generic_xss"),
   ("\"errorcomment\\u%\n&#AF;javascript:%", ⟨true, ["javascript:"], ["&#x?[0-9a-fA-F]+;"], .HIGH⟩, "&quot;errorcomment\\u%\n&amp;#AF;javascript:%", "comment_xss"),
   ("errorAF12 comment\n%12\t%", ⟨true, [], ["%[0-9a-fA-F]{2}"], .MEDIUM⟩, "errorAF12 comment\n%12\t%", "comment_xss"),
   ("'</script>AF\"", ⟨false, [], [], .LOW⟩, "&#x27;&lt;/script&gt;AF&quot;", "generic_xss"),
   ("\t>>\"\nxjavascript:;comment", ⟨true, ["javascript:"], [], .HIGH⟩, "\t&gt;&gt;&quot;\nxjavascript:;comment", "comment_xss"),
   ("\\u\"on';&#\t&#&#scripté", ⟨false, [], [], .LOW⟩, "\\u&quot;on&#x27;;&amp;#\t&amp;#&amp;#scripté", "generic_xss"),
   ("&#\"AF", ⟨false, [], [], .LOW⟩, "&amp;#&quot;AF", "generic_xss"),
   ("comment\n\n", ⟨false, [], [], .LOW⟩, "comment\n\n", "comment_xss"),
   ("\\uAF</script>", ⟨false, [], [], .LOW⟩, "\\uAF&lt;/script&gt;", "generic_xss"),
   (" ", ⟨false, [], [], .LOW⟩, " ", "generic_xss"),
   ("; \n'javascript:javascript:< script\n", ⟨true, ["javascript:"], [], .HIGH⟩, "; \n&#x27;javascript:javascript:&lt; script\n", "generic_xss"),
   ("'é", ⟨false, [], [], .LOW⟩, "&#x27;é", "generic_xss"),
   (" \t\n>", ⟨false, [], [], .LOW⟩, " \t\n&gt;", "generic_xss"),
   ("中%comment<é&#", ⟨false, [], [], .LOW⟩, "中%comment&lt;é&amp;#", "comment_xss"),
   ("\t\\x\\u12", ⟨false, [], [], .LOW⟩, "\t\\x\\u12", "generic_xss"),
   ("AF;12commentxerror\\xAF中", ⟨true, [], ["\\\\x[0-9a-fA-F]{2}"], .MEDIUM⟩, "AF;12commentxerror\\xAF中", "comment_xss"),
   (";x<on\"</script>", ⟨false, [], [], .LOW⟩, ";x&lt;on&quot;&lt;/script&gt;", "generic_xss"),
   ("\\x javascript: =\\u&#errorcomment>", ⟨true, ["javascript:"], [], .HIGH⟩, "\\x javascript: =\\u&amp;#errorcomment&gt;", "comment_xss")]

-- PBT: independent executable expectations for detection, escaping and routing.
example : (pythonOracle.all fun (s, d, escaped, kind) =>
    detect_xss_patterns testApp s == d && htmlEscape s == escaped &&
    (unsafe_xss_handling testApp s).type == kind) = true := by native_decide
#eval (pythonOracle.length, pythonOracle.all fun (s, d, escaped, kind) =>
  detect_xss_patterns testApp s == d && htmlEscape s == escaped &&
  (unsafe_xss_handling testApp s).type == kind)

/-! ## Correctness -/

theorem correctness (app : WebApplication) (input : String) :
    Pre app input → Post_prop app input := by
  intro _
  exact ⟨handling_thm app input, detection_thm app input, recognition_thm app input, escape_thm input,
    fun other => state_thm app other input,
    fun later => rendering_thm app _ _ later⟩

/-! ## Imperative implementation

These implementations use mutable state and real `for` loops. They do not call
the functional renderer or functional detector. The recognizer itself is shared.
-/

def render_template_imp (_app : WebApplication) (template : String) (context : Context) : String := Id.run do
  let mut rendered := template
  for entry in context do
    rendered := substitute rendered entry
  return rendered

def escapeContext_imp (context : Context) : Context := Id.run do
  let mut safe_context : Context := []
  for (key, value) in context do
    safe_context := safe_context ++ [(key, htmlEscape value)]
  return safe_context

def safe_render_template_imp (_app : WebApplication) (template : String) (context : Context) : String := Id.run do
  let safe_context := escapeContext_imp context
  let mut rendered := template
  for entry in safe_context do
    rendered := substitute rendered entry
  return rendered

def detected_imp (patterns : List (String × Regex)) (input : String) : List String := Id.run do
  let mut found : List String := []
  for (pattern, regex) in patterns do
    found := if regexSearch regex input then found ++ [pattern] else found
  return found

def detect_xss_patterns_imp (_app : WebApplication) (input : String) : Detection := Id.run do
  let scripts := detected_imp scriptPatterns input
  let encoded := detected_imp encodedPatterns input
  let mut risk := Risk.LOW
  if !scripts.isEmpty then
    risk := .HIGH
  else if !encoded.isEmpty then
    risk := .MEDIUM
  return ⟨!scripts.isEmpty || !encoded.isEmpty, scripts, encoded, risk⟩

def unsafe_xss_handling_imp (app : WebApplication) (input : String) : Result := Id.run do
  let detection := detect_xss_patterns_imp app input
  let mut kind := "generic_xss"
  let mut template := genericTemplate
  let mut context := Scenario.generic.context input
  if containsText (routeLower input) "comment" then
    kind := "comment_xss"
    template := commentTemplate
    context := Scenario.comment.context input
  else if containsText (routeLower input) "search" then
    kind := "search_xss"
    template := searchTemplate
    context := Scenario.search.context input
  else if containsText (routeLower input) "profile" then
    kind := "profile_xss"
    template := profileTemplate
    context := Scenario.profile.context input
  let rendered := render_template_imp app template context
  return ⟨kind, rendered, detection, true⟩

/-! ## Imperative tests -/

example : check unsafe_xss_handling_imp = true := by native_decide
example : safe_render_template_imp testApp "{{{x}}}" [("x", "<script>'&")] =
    "{&lt;script&gt;&#x27;&amp;}" := by native_decide
example : corpus.all (fun s => unsafe_xss_handling testApp s == unsafe_xss_handling_imp testApp s) = true := by native_decide
example : (contexts.all fun c => safe_render_template testApp "{{x}} {{y}}" c ==
    safe_render_template_imp testApp "{{x}} {{y}}" c) = true := by native_decide
#eval check unsafe_xss_handling_imp

/-! ## Loop invariants and functional/imperative equivalence -/

theorem append_map_fold {α β : Type} (f : α → β) (xs : List α) (acc : List β) :
    xs.foldl (fun out x => out ++ [f x]) acc = acc ++ xs.map f := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih => simp [List.foldl_cons, ih, List.append_assoc]

theorem append_filter_map_fold {α β : Type} (p : α → Bool) (f : α → β)
    (xs : List α) (acc : List β) :
    xs.foldl (fun out x => if p x then out ++ [f x] else out) acc =
      acc ++ (xs.filter p).map f := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
    cases hp : p x <;> simp [List.foldl_cons, hp, ih, List.append_assoc]

theorem render_equivalence (app : WebApplication) (template : String) (context : Context) :
    render_template app template context = render_template_imp app template context := by
  simp [render_template, render_template_imp]

theorem escapeContext_equivalence (context : Context) :
    escapeContext context = escapeContext_imp context := by
  unfold escapeContext_imp
  simp only [pure_bind, bind_pure, List.forIn_pure_yield_eq_foldl]
  change escapeContext context = context.foldl (fun out x => out ++ [(x.1, htmlEscape x.2)]) []
  rw [append_map_fold]
  rfl

theorem safe_render_equivalence (app : WebApplication) (template : String) (context : Context) :
    safe_render_template app template context = safe_render_template_imp app template context := by
  simp [safe_render_template, safe_render_template_imp, render_template, ← escapeContext_equivalence]

theorem detected_equivalence (patterns : List (String × Regex)) (input : String) :
    detected patterns input = detected_imp patterns input := by
  unfold detected_imp
  simp only [pure_bind, bind_pure, List.forIn_pure_yield_eq_foldl]
  change detected patterns input = patterns.foldl
    (fun out x => if regexSearch x.2 input then out ++ [x.1] else out) []
  rw [append_filter_map_fold]
  rfl

theorem detector_equivalence (app : WebApplication) (input : String) :
    detect_xss_patterns app input = detect_xss_patterns_imp app input := by
  cases hs : detected scriptPatterns input <;>
    cases he : detected encodedPatterns input <;>
    simp [detect_xss_patterns, detect_xss_patterns_imp, ← detected_equivalence, detectionFrom, hs, he]

theorem equivalence (app : WebApplication) (input : String) :
    unsafe_xss_handling app input = unsafe_xss_handling_imp app input := by
  by_cases hc : containsText (routeLower input) "comment" = true
  · simp [unsafe_xss_handling, unsafe_xss_handling_imp, scenario, hc,
      Scenario.typeName, Scenario.template, ← render_equivalence, ← detector_equivalence]
  · by_cases hs : containsText (routeLower input) "search" = true
    · simp [unsafe_xss_handling, unsafe_xss_handling_imp, scenario, hc, hs,
        Scenario.typeName, Scenario.template, ← render_equivalence, ← detector_equivalence]
    · by_cases hp : containsText (routeLower input) "profile" = true <;>
        simp [unsafe_xss_handling, unsafe_xss_handling_imp, scenario, hc, hs, hp,
          Scenario.typeName, Scenario.template, ← render_equivalence, ← detector_equivalence]

end CrossSiteScripting
end Agent
