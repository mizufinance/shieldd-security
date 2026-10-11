import ShielddSecurity.BooleanHints207
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedBooleanSlots208B0005
open BooleanHints207 CompilerAssertionBlock51 CompilerArithmeticTransport41
def slots : List (Nat × Nat) := [(1280,1320),(1281,1321),(1282,1322),(1283,1323),(1284,1324),(1285,1325),(1286,1326),(1287,1327),(1288,1328),(1289,1329),(1290,1330),(1291,1331),(1292,1332),(1293,1333),(1294,1334),(1295,1335),(1296,1336),(1297,1337),(1298,1338),(1299,1339),(1300,1340),(1301,1341),(1302,1342),(1303,1343),(1304,1344),(1305,1345),(1306,1346),(1307,1347),(1308,1348),(1309,1349),(1310,1350),(1311,1351),(1312,1352),(1313,1353),(1314,1354),(1315,1355),(1316,1356),(1317,1357),(1318,1358),(1319,1359),(1320,1360),(1321,1361),(1322,1362),(1323,1363),(1324,1364),(1325,1365),(1326,1366),(1327,1367),(1328,1368),(1329,1369),(1330,1370),(1333,1371),(1336,1373),(1337,1375),(1338,1376),(1339,1377),(1340,1378),(1341,1379),(1342,1380),(1343,1381),(1344,1382),(1345,1383),(1346,1384),(1347,1385),(1348,1386),(1349,1387),(1350,1388),(1351,1389),(1352,1390),(1353,1391),(1354,1392),(1355,1393),(1356,1394),(1357,1395),(1358,1396),(1359,1397),(1360,1398),(1361,1399),(1362,1400),(1363,1401),(1364,1402),(1365,1403),(1366,1404),(1367,1405),(1368,1406),(1369,1407),(1370,1408),(1371,1409),(1372,1410),(1373,1411),(1374,1412),(1375,1413),(1376,1414),(1377,1415),(1378,1416),(1379,1417),(1380,1418),(1381,1419),(1382,1420),(1383,1421),(1384,1422),(1385,1423),(1386,1424),(1387,1425),(1388,1426),(1389,1427),(1390,1428),(1391,1429),(1392,1430),(1393,1431),(1394,1432),(1395,1433),(1396,1434),(1397,1435),(1398,1436),(1399,1437),(1400,1438),(1401,1439),(1402,1440),(1403,1441),(1404,1442),(1405,1443),(1406,1444),(1407,1445),(1408,1446),(1409,1447),(1410,1448),(1411,1449),(1412,1450),(1413,1451),(1414,1452),(1415,1453),(1416,1454),(1417,1455),(1418,1456),(1419,1457),(1420,1458),(1421,1459),(1422,1460),(1423,1461),(1424,1462),(1425,1463),(1426,1464),(1427,1465),(1428,1466),(1429,1467),(1430,1468),(1431,1469),(1432,1470),(1433,1471),(1434,1472),(1435,1473),(1436,1474),(1437,1475),(1438,1476),(1439,1477),(1440,1478),(1441,1479),(1442,1480),(1443,1481),(1444,1482),(1445,1483),(1446,1484),(1447,1485),(1448,1486),(1449,1487),(1450,1488),(1451,1489),(1452,1490),(1453,1491),(1454,1492),(1455,1493),(1456,1494),(1457,1495),(1458,1496),(1459,1497),(1460,1498),(1461,1499),(1462,1500),(1463,1501),(1464,1502),(1490,1579),(1491,1580),(1492,1581),(1493,1582),(1494,1583),(1495,1584),(1496,1585),(1497,1586),(1498,1587),(1499,1588),(1500,1589),(1501,1590),(1502,1591),(1503,1592),(1504,1593),(1505,1594),(1506,1595),(1507,1596),(1508,1597),(1509,1598),(1510,1599),(1511,1600),(1512,1601),(1513,1602),(1514,1603),(1515,1604),(1516,1605),(1517,1606),(1518,1607),(1519,1608),(1520,1609),(1521,1610),(1525,1611),(1526,1612),(1527,1613),(1528,1614),(1529,1615),(1530,1616),(1531,1617),(1532,1618),(1533,1619),(1534,1620),(1535,1621)]
theorem count : slots.length=224 := rfl
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
end ShielddSecurity.CapturedBooleanSlots208B0005

set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0005.slots
#print axioms ShielddSecurity.CapturedBooleanSlots208B0005.slots
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0005.count
#print axioms ShielddSecurity.CapturedBooleanSlots208B0005.count
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0005.checked
#print axioms ShielddSecurity.CapturedBooleanSlots208B0005.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0005.originals
#print axioms ShielddSecurity.CapturedBooleanSlots208B0005.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0005.positions
#print axioms ShielddSecurity.CapturedBooleanSlots208B0005.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0005.constructor
#print axioms ShielddSecurity.CapturedBooleanSlots208B0005.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0005.sound
#print axioms ShielddSecurity.CapturedBooleanSlots208B0005.sound
