import ShielddSecurity.BooleanHints207
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedBooleanSlots208B0007
open BooleanHints207 CompilerAssertionBlock51 CompilerArithmeticTransport41
def slots : List (Nat × Nat) := [(1792,1861),(1793,1862),(1794,1863),(1795,1864),(1796,1865),(1797,1866),(1798,1867),(1799,1868),(1800,1869),(1801,1870),(1802,1871),(1803,1872),(1804,1873),(1805,1874),(1806,1875),(1807,1876),(1808,1877),(1809,1878),(1810,1879),(1811,1880),(1812,1881),(1813,1882),(1814,1883),(1815,1884),(1816,1885),(1817,1886),(1818,1887),(1819,1888),(1820,1889),(1821,1890),(1822,1891),(1823,1892),(1824,1893),(1825,1894),(1826,1895),(1827,1896),(1828,1897),(1829,1898),(1830,1899),(1831,1900),(1832,1901),(1833,1902),(1834,1903),(1835,1904),(1836,1905),(1837,1906),(1838,1907),(1839,1908),(1840,1909),(1841,1910),(1842,1911),(1843,1912),(1844,1913),(1845,1914),(1846,1915),(1847,1916),(1848,1917),(1849,1918),(1850,1919),(1851,1920),(1852,1921),(1853,1922),(1854,1923),(1855,1924),(1856,1925),(1857,1926),(1858,1927),(1859,1928),(1860,1929),(1861,1930),(1862,1931),(1863,1932),(1864,1933),(1865,1934),(1866,1935),(1867,1936),(1868,1937),(1869,1938),(1870,1939),(1871,1940),(1872,1941),(1873,1942),(1874,1943),(1875,1944),(1876,1945),(1877,1946),(1878,1947),(1879,1948),(1880,1949),(1881,1950),(1882,1951),(1883,1952),(1884,1953),(1885,1954),(1886,1955),(1887,1956),(1888,1957),(1889,1958),(1890,1959),(1891,1960),(1892,1961),(1893,1962),(1894,1963),(1895,1964),(1896,1965),(1897,1966),(1898,1967),(1899,1968),(1900,1969),(1901,1970),(1902,1971),(1903,1972),(1904,1973),(1905,1974),(1906,1975),(1907,1976),(1908,1977),(1909,1978),(1910,1979),(1991,1996),(1992,1997),(1993,1998),(1994,1999),(1998,2000),(1999,2001),(2000,2002),(2001,2003),(2002,2004),(2003,2005),(2004,2006),(2005,2007),(2006,2008),(2007,2009),(2008,2010),(2009,2011),(2010,2012),(2011,2013),(2012,2014),(2013,2015),(2014,2016),(2015,2017),(2016,2018),(2017,2019),(2018,2020),(2019,2021),(2020,2022),(2021,2023),(2022,2024),(2023,2025),(2024,2026),(2025,2027),(2026,2028),(2027,2029),(2028,2030),(2029,2031),(2030,2032),(2031,2033),(2032,2034),(2033,2035),(2034,2036),(2035,2037),(2036,2038),(2037,2039),(2038,2040),(2039,2041),(2040,2042),(2041,2043),(2042,2044),(2043,2045),(2044,2046),(2045,2047),(2046,2048),(2047,2049)]
theorem count : slots.length=173 := rfl
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
end ShielddSecurity.CapturedBooleanSlots208B0007

set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0007.slots
#print axioms ShielddSecurity.CapturedBooleanSlots208B0007.slots
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0007.count
#print axioms ShielddSecurity.CapturedBooleanSlots208B0007.count
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0007.checked
#print axioms ShielddSecurity.CapturedBooleanSlots208B0007.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0007.originals
#print axioms ShielddSecurity.CapturedBooleanSlots208B0007.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0007.positions
#print axioms ShielddSecurity.CapturedBooleanSlots208B0007.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0007.constructor
#print axioms ShielddSecurity.CapturedBooleanSlots208B0007.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0007.sound
#print axioms ShielddSecurity.CapturedBooleanSlots208B0007.sound
