import ShielddSecurity.BooleanHints207
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedBooleanSlots208B0004
open BooleanHints207 CompilerAssertionBlock51 CompilerArithmeticTransport41
def slots : List (Nat × Nat) := [(1024,1067),(1025,1068),(1026,1069),(1027,1070),(1028,1071),(1029,1072),(1030,1073),(1031,1074),(1032,1075),(1033,1076),(1034,1077),(1035,1078),(1036,1079),(1037,1080),(1038,1081),(1039,1082),(1040,1083),(1041,1084),(1042,1085),(1043,1086),(1044,1087),(1045,1088),(1046,1089),(1047,1090),(1048,1091),(1049,1092),(1050,1093),(1051,1094),(1052,1095),(1053,1096),(1054,1097),(1055,1098),(1056,1099),(1057,1100),(1058,1101),(1059,1102),(1060,1103),(1061,1104),(1062,1105),(1063,1106),(1064,1107),(1065,1108),(1066,1109),(1069,1110),(1072,1112),(1073,1114),(1074,1115),(1075,1116),(1076,1117),(1077,1118),(1078,1119),(1079,1120),(1080,1121),(1081,1122),(1082,1123),(1083,1124),(1084,1125),(1085,1126),(1086,1127),(1087,1128),(1088,1129),(1089,1130),(1090,1131),(1091,1132),(1092,1133),(1093,1134),(1094,1135),(1095,1136),(1096,1137),(1097,1138),(1098,1139),(1099,1140),(1100,1141),(1101,1142),(1102,1143),(1103,1144),(1104,1145),(1105,1146),(1106,1147),(1107,1148),(1108,1149),(1109,1150),(1110,1151),(1111,1152),(1112,1153),(1113,1154),(1114,1155),(1115,1156),(1116,1157),(1117,1158),(1118,1159),(1119,1160),(1120,1161),(1121,1162),(1122,1163),(1123,1164),(1124,1165),(1125,1166),(1126,1167),(1127,1168),(1128,1169),(1129,1170),(1130,1171),(1131,1172),(1132,1173),(1133,1174),(1134,1175),(1135,1176),(1136,1177),(1137,1178),(1138,1179),(1139,1180),(1140,1181),(1141,1182),(1142,1183),(1143,1184),(1144,1185),(1145,1186),(1146,1187),(1147,1188),(1148,1189),(1149,1190),(1150,1191),(1151,1192),(1152,1193),(1153,1194),(1154,1195),(1155,1196),(1156,1197),(1157,1198),(1158,1199),(1159,1200),(1160,1201),(1161,1202),(1162,1203),(1163,1204),(1164,1205),(1165,1206),(1166,1207),(1167,1208),(1168,1209),(1169,1210),(1170,1211),(1171,1212),(1172,1213),(1173,1214),(1174,1215),(1175,1216),(1176,1217),(1177,1218),(1178,1219),(1179,1220),(1180,1221),(1181,1222),(1182,1223),(1183,1224),(1184,1225),(1185,1226),(1186,1227),(1187,1228),(1188,1229),(1189,1230),(1190,1231),(1191,1232),(1192,1233),(1193,1234),(1194,1235),(1195,1236),(1196,1237),(1197,1238),(1198,1239),(1199,1240),(1200,1241),(1203,1242),(1204,1244),(1205,1245),(1206,1246),(1207,1247),(1208,1248),(1209,1249),(1210,1250),(1211,1251),(1212,1252),(1213,1253),(1214,1254),(1215,1255),(1216,1256),(1217,1257),(1218,1258),(1219,1259),(1220,1260),(1221,1261),(1222,1262),(1223,1263),(1224,1264),(1225,1265),(1226,1266),(1227,1267),(1228,1268),(1229,1269),(1230,1270),(1231,1271),(1232,1272),(1233,1273),(1234,1274),(1235,1275),(1236,1276),(1237,1277),(1238,1278),(1239,1279),(1240,1280),(1241,1281),(1242,1282),(1243,1283),(1244,1284),(1245,1285),(1246,1286),(1247,1287),(1248,1288),(1249,1289),(1250,1290),(1251,1291),(1252,1292),(1253,1293),(1254,1294),(1255,1295),(1256,1296),(1257,1297),(1258,1298),(1259,1299),(1260,1300),(1261,1301),(1262,1302),(1263,1303),(1264,1304),(1265,1305),(1266,1306),(1267,1307),(1268,1308),(1269,1309),(1270,1310),(1271,1311),(1272,1312),(1273,1313),(1274,1314),(1275,1315),(1276,1316),(1277,1317),(1278,1318),(1279,1319)]
theorem count : slots.length=250 := rfl
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
end ShielddSecurity.CapturedBooleanSlots208B0004

set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0004.slots
#print axioms ShielddSecurity.CapturedBooleanSlots208B0004.slots
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0004.count
#print axioms ShielddSecurity.CapturedBooleanSlots208B0004.count
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0004.checked
#print axioms ShielddSecurity.CapturedBooleanSlots208B0004.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0004.originals
#print axioms ShielddSecurity.CapturedBooleanSlots208B0004.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0004.positions
#print axioms ShielddSecurity.CapturedBooleanSlots208B0004.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0004.constructor
#print axioms ShielddSecurity.CapturedBooleanSlots208B0004.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0004.sound
#print axioms ShielddSecurity.CapturedBooleanSlots208B0004.sound
