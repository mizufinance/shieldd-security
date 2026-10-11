import ShielddSecurity.BooleanHints207
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedBooleanSlots208B0008
open BooleanHints207 CompilerAssertionBlock51 CompilerArithmeticTransport41
def slots : List (Nat × Nat) := [(2048,2050),(2049,2051),(2050,2052),(2051,2053),(2052,2054),(2053,2055),(2054,2056),(2055,2057),(2056,2058),(2057,2059),(2058,2060),(2059,2061),(2060,2062),(2061,2063),(2062,2064),(2063,2065),(2064,2066),(2065,2067),(2066,2068),(2067,2069),(2068,2070),(2069,2071),(2070,2072),(2071,2073),(2072,2074),(2073,2075),(2074,2076),(2075,2077),(2076,2078),(2077,2079),(2078,2080),(2079,2081),(2080,2082),(2081,2083),(2082,2084),(2083,2085),(2084,2086),(2085,2087),(2086,2088),(2087,2089),(2088,2090),(2089,2091),(2090,2092),(2091,2093),(2092,2094),(2093,2095),(2094,2096),(2095,2097),(2096,2098),(2097,2099),(2098,2100),(2099,2101),(2100,2102),(2101,2103),(2102,2104),(2103,2105),(2104,2106),(2105,2107),(2106,2108),(2107,2109),(2108,2110),(2109,2111),(2110,2112),(2111,2113),(2112,2114),(2113,2115),(2114,2116),(2115,2117),(2116,2118),(2117,2119),(2118,2120),(2119,2121),(2120,2122),(2121,2123),(2122,2124),(2123,2125),(2124,2126),(2125,2127),(2126,2128),(2127,2129),(2128,2130),(2129,2131),(2130,2132),(2131,2133),(2132,2134),(2133,2135),(2134,2136),(2135,2137),(2136,2138),(2137,2139),(2138,2140),(2139,2141),(2140,2142),(2141,2143),(2142,2144),(2143,2145),(2144,2146),(2145,2147),(2146,2148),(2147,2149),(2148,2150),(2149,2151),(2150,2152),(2151,2153),(2152,2154),(2153,2155),(2154,2156),(2155,2157),(2156,2158),(2157,2159),(2158,2160),(2159,2161),(2160,2162),(2161,2163),(2162,2164),(2163,2165),(2164,2166),(2165,2167),(2166,2168),(2167,2169),(2168,2170),(2169,2171),(2170,2172),(2171,2173),(2172,2174),(2173,2175),(2174,2176),(2175,2177),(2176,2178),(2177,2179),(2178,2180),(2179,2181),(2180,2182),(2181,2183),(2182,2184),(2183,2185),(2184,2186),(2185,2187),(2186,2188),(2187,2189),(2188,2190),(2189,2191),(2190,2192),(2191,2193),(2192,2194),(2193,2195),(2194,2196),(2195,2197),(2196,2198),(2197,2199),(2198,2200),(2199,2201),(2200,2202),(2201,2203),(2202,2204),(2203,2205),(2204,2206),(2205,2207),(2206,2208),(2207,2209),(2208,2210),(2209,2211),(2210,2212),(2211,2213),(2212,2214),(2213,2215),(2214,2216),(2215,2217),(2216,2218),(2217,2219),(2218,2220),(2219,2221),(2220,2222),(2221,2223),(2222,2224),(2223,2225),(2224,2226),(2225,2227),(2226,2228),(2227,2229),(2228,2230),(2229,2231),(2230,2232),(2231,2233),(2232,2234),(2233,2235),(2234,2236),(2235,2237),(2236,2238),(2237,2239),(2238,2240),(2239,2241),(2240,2242),(2241,2243),(2242,2244),(2243,2245),(2244,2246),(2245,2247),(2246,2248),(2247,2249),(2248,2250),(2249,2251)]
theorem count : slots.length=202 := rfl
theorem checked : checkSlots CapturedFullAssertions54.recipeAt slots=true := by decide
theorem originals : ∀ slot∈slots,3≤slot.2 ∧ slot.2<22738 := by decide
theorem positions : ∀ slot∈slots,slot.1<22816 := by decide
variable {F : Type} [Field F] [CharP F p]
theorem constructor (base : Nat → F) (bits : Nat → Bool) (columns : List Nat)
 (coverage : ∀ slot∈slots,slot.2∈columns) : ∀ slot∈slots,
 ∃ row,CapturedFullRelation58.rowAt (177954+slot.1)=some row ∧
 Square (eval (CapturedFullRelation58.candidate (seeded base bits columns)) row.a)
        (eval (CapturedFullRelation58.candidate (seeded base bits columns)) row.b) :=
 fun slot member => candidate_selected base bits columns slots checked originals coverage positions slot member
theorem sound (rho : Nat → F)
 (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 ∀ slot∈slots,rho slot.2=0 ∨ rho slot.2=1 := by
 intro slot member
 obtain ⟨outlined,matching⟩:=checked_slot _ slots checked slot member
 have truth:=((CapturedFullRelation58.satisfies_iff rho).mp satisfied).2 slot.1
   (positions slot member) (outlined,wireRecipe slot.2) matching
 exact (wire_truth rho slot.2).mp truth
end ShielddSecurity.CapturedBooleanSlots208B0008

set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0008.slots
#print axioms ShielddSecurity.CapturedBooleanSlots208B0008.slots
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0008.count
#print axioms ShielddSecurity.CapturedBooleanSlots208B0008.count
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0008.checked
#print axioms ShielddSecurity.CapturedBooleanSlots208B0008.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0008.originals
#print axioms ShielddSecurity.CapturedBooleanSlots208B0008.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0008.positions
#print axioms ShielddSecurity.CapturedBooleanSlots208B0008.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0008.constructor
#print axioms ShielddSecurity.CapturedBooleanSlots208B0008.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0008.sound
#print axioms ShielddSecurity.CapturedBooleanSlots208B0008.sound
