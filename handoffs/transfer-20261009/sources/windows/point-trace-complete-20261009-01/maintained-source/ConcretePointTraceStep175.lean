import ShielddSecurity.ConcretePointTraceStep174
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep175
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 7297327363126440184922607716418021756610312426286230966214985252248030418469
def inputY : F := 14242845392920676566693420597489916148817088957451360961979646970934300628623
def doubleX : F := 9062797992490822316923044828891601598650697223370077572484207595553547847968
def doubleY : F := 52428550146815033727108879315355295143920981882188102558262944085998294208997
def doubleSlope : F := 14238102965855493698851172484756715743594360145673435320648146752440761628536
def addX : F := 26676143068213058137815775796005897050710670109559509647531094584251080299120
def addY : F := 50408293294553225393996623042617029869269350007292622811372669154651582664045
def addSlope : F := 47129599231502339026009977543930565137969449911357365484757062727212416504323
def outX : F := 26676143068213058137815775796005897050710670109559509647531094584251080299120
def outY : F := 50408293294553225393996623042617029869269350007292622811372669154651582664045

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((43373939347114979545965612596808935006304871487792704 : Nat) • base) + ((43373939347114979545965612596808935006304871487792704 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep174.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (14242845392920676566693420597489916148817088957451360961979646970934300628623 : Int)) * (21241459849916133134707794625689260300507144025240906450161882059662406299505 : Int) =
        (1 : Int) + (11539383200980756495249127782251814334879618263315801155947880009127021571133 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (14238102965855493698851172484756715743594360145673435320648146752440761628536 : Int) * ((2 : Int) * (14242845392920676566693420597489916148817088957451360961979646970934300628623 : Int)) =
        (3 : Int) * (7297327363126440184922607716418021756610312426286230966214985252248030418469 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (7297327363126440184922607716418021756610312426286230966214985252248030418469 : Int) + (-40964 : Int) * (-40964 : Int) + (4688187957336539687541524304593284728901655505165025869103608695876746761797 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (9062797992490822316923044828891601598650697223370077572484207595553547847968 : Int) =
        (14238102965855493698851172484756715743594360145673435320648146752440761628536 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (7297327363126440184922607716418021756610312426286230966214985252248030418469 : Int) - (7297327363126440184922607716418021756610312426286230966214985252248030418469 : Int) + (-3866123629847761723213777439521644531271697512355281172088598304275519558366 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (52428550146815033727108879315355295143920981882188102558262944085998294208997 : Int) =
        (14238102965855493698851172484756715743594360145673435320648146752440761628536 : Int) * ((7297327363126440184922607716418021756610312426286230966214985252248030418469 : Int) - (9062797992490822316923044828891601598650697223370077572484207595553547847968 : Int)) - (14242845392920676566693420597489916148817088957451360961979646970934300628623 : Int) + (479384629704967645210932446324103233151228735678579795641298365930646813468 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem next_add : ∃ output : curve.Equation addX addY,
    (((43373939347114979545965612596808935006304871487792704 : Nat) • base) + ((43373939347114979545965612596808935006304871487792704 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨doubleValid, doubled⟩ := next_double
  have different : doubleX ≠ baseX := by
    apply sub_ne_zero.mp
    have integer : ((9062797992490822316923044828891601598650697223370077572484207595553547847968 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) * (7403230075259380283192786337659100670585125823762285729350531687590979163547 : Int) =
        (1 : Int) + (-4322760998237527807378358119561187772539501960508250373618813639622889705762 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have slopeRow : addSlope * (doubleX - baseX) = doubleY - baseY := by
    have integer : (47129599231502339026009977543930565137969449911357365484757062727212416504323 : Int) * ((9062797992490822316923044828891601598650697223370077572484207595553547847968 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int)) =
        (52428550146815033727108879315355295143920981882188102558262944085998294208997 : Int) - (43044799768094727361329244498846272665229388789665544224645223436242971151146 : Int) + (-27519068210691232738676981477085071689558296078012837092933990811935563052692 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have xRow : addX = addSlope ^ 2 - A * B - doubleX - baseX := by
    have integer : (26676143068213058137815775796005897050710670109559509647531094584251080299120 : Int) =
        (47129599231502339026009977543930565137969449911357365484757062727212416504323 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (9062797992490822316923044828891601598650697223370077572484207595553547847968 : Int) - (39680211447325986415026918192437531897852916166128269978655486138252525496083 : Int) + (-42360294670464235260380035202493025853159429808016540834652573002292206299502 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  have yRow : addY = addSlope * (doubleX - addX) - doubleY := by
    have integer : (50408293294553225393996623042617029869269350007292622811372669154651582664045 : Int) =
        (47129599231502339026009977543930565137969449911357365484757062727212416504323 : Int) * ((9062797992490822316923044828891601598650697223370077572484207595553547847968 : Int) - (26676143068213058137815775796005897050710670109559509647531094584251080299120 : Int)) - (52428550146815033727108879315355295143920981882188102558262944085998294208997 : Int) + (15830953364896259255175701744905238723002948675214562092424664234209731746626 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, addX, addY, addSlope, outX, outY] using equal
  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [doubled]
  exact added

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (86747878694229959091931225193617870012609742975585409 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, addX, addY, show (86747878694229959091931225193617870012609742975585409 : Nat) = 43373939347114979545965612596808935006304871487792704 + 43373939347114979545965612596808935006304871487792704 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add

end ShielddSecurity.ConcretePointTraceStep175
