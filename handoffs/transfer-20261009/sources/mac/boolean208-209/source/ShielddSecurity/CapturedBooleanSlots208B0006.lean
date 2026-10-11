import ShielddSecurity.BooleanHints207
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedBooleanSlots208B0006
open BooleanHints207 CompilerAssertionBlock51 CompilerArithmeticTransport41
def slots : List (Nat × Nat) := [(1536,1622),(1537,1623),(1538,1624),(1539,1625),(1540,1626),(1541,1627),(1542,1628),(1543,1629),(1544,1630),(1545,1631),(1546,1632),(1547,1633),(1548,1634),(1549,1635),(1550,1636),(1551,1637),(1552,1638),(1553,1639),(1554,1640),(1555,1641),(1556,1642),(1557,1643),(1558,1644),(1559,1645),(1560,1646),(1561,1647),(1562,1648),(1563,1649),(1564,1650),(1565,1651),(1566,1652),(1567,1653),(1568,1654),(1569,1655),(1570,1656),(1571,1657),(1572,1658),(1573,1659),(1574,1660),(1575,1661),(1576,1662),(1577,1663),(1578,1664),(1579,1665),(1580,1666),(1581,1667),(1582,1668),(1583,1669),(1584,1670),(1585,1671),(1586,1672),(1587,1673),(1588,1674),(1589,1675),(1590,1676),(1591,1677),(1592,1678),(1593,1679),(1594,1680),(1595,1681),(1596,1682),(1597,1683),(1598,1684),(1599,1685),(1600,1686),(1601,1687),(1602,1688),(1603,1689),(1604,1690),(1605,1691),(1606,1692),(1607,1693),(1608,1694),(1609,1695),(1610,1696),(1611,1697),(1612,1698),(1613,1699),(1614,1700),(1615,1701),(1616,1702),(1617,1703),(1618,1704),(1619,1705),(1620,1706),(1621,1707),(1622,1708),(1623,1709),(1624,1710),(1625,1711),(1626,1712),(1627,1713),(1628,1714),(1629,1715),(1630,1716),(1631,1717),(1632,1718),(1633,1719),(1634,1720),(1635,1721),(1636,1722),(1637,1723),(1638,1724),(1639,1725),(1640,1726),(1641,1727),(1642,1728),(1643,1729),(1644,1730),(1645,1731),(1646,1732),(1647,1733),(1648,1734),(1649,1735),(1650,1736),(1651,1737),(1652,1738),(1653,1739),(1654,1740),(1655,1741),(1745,1817),(1746,1818),(1747,1819),(1748,1820),(1749,1821),(1750,1822),(1751,1823),(1752,1824),(1753,1825),(1754,1826),(1755,1827),(1756,1828),(1757,1829),(1758,1830),(1759,1831),(1760,1832),(1761,1833),(1762,1834),(1763,1835),(1764,1836),(1765,1837),(1766,1838),(1767,1839),(1768,1840),(1769,1841),(1770,1842),(1771,1843),(1772,1844),(1773,1845),(1774,1846),(1775,1847),(1776,1848),(1780,1849),(1781,1850),(1782,1851),(1783,1852),(1784,1853),(1785,1854),(1786,1855),(1787,1856),(1788,1857),(1789,1858),(1790,1859),(1791,1860)]
theorem count : slots.length=164 := rfl
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
end ShielddSecurity.CapturedBooleanSlots208B0006

set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0006.slots
#print axioms ShielddSecurity.CapturedBooleanSlots208B0006.slots
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0006.count
#print axioms ShielddSecurity.CapturedBooleanSlots208B0006.count
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0006.checked
#print axioms ShielddSecurity.CapturedBooleanSlots208B0006.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0006.originals
#print axioms ShielddSecurity.CapturedBooleanSlots208B0006.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0006.positions
#print axioms ShielddSecurity.CapturedBooleanSlots208B0006.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0006.constructor
#print axioms ShielddSecurity.CapturedBooleanSlots208B0006.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0006.sound
#print axioms ShielddSecurity.CapturedBooleanSlots208B0006.sound
