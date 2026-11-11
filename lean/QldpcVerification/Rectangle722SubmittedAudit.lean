import Lean.Elab.GuardMsgs
import QldpcVerification.Rectangle722Submitted

/-! Pending external capped replay; these guards reject additional axioms. -/

/-- info: 'QldpcVerification.Rectangle722Submitted.HX_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Rectangle722Submitted.HX_eq

/-- info: 'QldpcVerification.Rectangle722Submitted.HZ_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Rectangle722Submitted.HZ_eq

/-- info: 'QldpcVerification.Rectangle722Submitted.code_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Rectangle722Submitted.code_eq

/-- info: 'QldpcVerification.Rectangle722Submitted.rankX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Rectangle722Submitted.rankX

/-- info: 'QldpcVerification.Rectangle722Submitted.rankZ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Rectangle722Submitted.rankZ

/-- info: 'QldpcVerification.Rectangle722Submitted.encoded_qubits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Rectangle722Submitted.encoded_qubits

/-- info: 'QldpcVerification.Rectangle722Submitted.x_lower_fifteen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Rectangle722Submitted.x_lower_fifteen

/-- info: 'QldpcVerification.Rectangle722Submitted.z_lower_fifteen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Rectangle722Submitted.z_lower_fifteen

/-- info: 'QldpcVerification.Rectangle722Submitted.pauli_lower_fifteen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Rectangle722Submitted.pauli_lower_fifteen


/-
Source SHA-256 manifest for pending replay (not a successful build receipt).
Source limits: maxHeartbeats 800000; maxRecDepth 4096.
This revised helper awaits Lean replay. External replay must use a detached
allocation with enforced memory/swap limits and one local Lean thread;
the root capped runner must record the actual allocation limits and outcome.
e5c6801c04e6256888d7e869fcb4a7f1f15efc715cc03212639e4faba95254aa  scripts/gen_rectangle722.py
ab82cf13487aefe6fed1ce6f7f37b5e33890af0eee103000018410ca7012fe93  lean/QldpcVerification/Rectangle722Submitted.lean
724e31b2dd8d608964ee39f3f4acb0580d1972d3dcdb33772dc0a706c64c42e8  lean/QldpcVerification/Input/Rectangle722Recognition.lean
2df617e75be62d32394b213a83ffd300684ffdaaa19218b3f56976ef2d5711c5  lean/QldpcVerification/Input/Rectangle722Support.lean
79187b6382f53ed9914218a66c9e44436bd8644102ab36b8231e3e269953e0f4  lean/QldpcVerification/Input/Rectangle722X00.lean
c23aa725c0ad5656fb616b3dad697f7b71bb13fb6e181f3c386939e82e7f8ecb  lean/QldpcVerification/Input/Rectangle722X01.lean
bdb4d23ddd4987dc86e5ee0b808aa251e5f5d10fb88c00ffd6bc87c1e51fe392  lean/QldpcVerification/Input/Rectangle722X02.lean
64739ea06c4bcf6f76ce2f1a7e0446c06fe24b8d25ed603a1f0d927d0eb3e51f  lean/QldpcVerification/Input/Rectangle722X03.lean
dd18080205161b1009b9656faa53cd82d739b2a88a0d2225e4cb46e16766f225  lean/QldpcVerification/Input/Rectangle722X04.lean
4aeda5492e666fbcee14add41395225419832d69ab0d07ff68a97773695b88c1  lean/QldpcVerification/Input/Rectangle722X05.lean
1fe60674ddb5f9ffa53a9f2aeff1e6241f38ac23feaf8c86b494fa014d983359  lean/QldpcVerification/Input/Rectangle722X06.lean
03ebac327fc4dd3af4074c8793139e5625943e9d75c4117a279e47e92fdfc027  lean/QldpcVerification/Input/Rectangle722X07.lean
c22b223009f3adc011b5359299a0302f1e9374213053a7bbc3dd093e60020ced  lean/QldpcVerification/Input/Rectangle722X08.lean
323ce843fb1473bc6c3f54ec8461f53be702657a0101aeec1a0ba6e48412eb5d  lean/QldpcVerification/Input/Rectangle722X09.lean
b290952fe1d61e4bc6c0a7efc69807143c5e6d1d8442a2deaa906436d9d2f339  lean/QldpcVerification/Input/Rectangle722X10.lean
18ad456f3e1c46d9e1d816224b19d8cd79e1ca223ab583497a2cb24460bb65d8  lean/QldpcVerification/Input/Rectangle722X11.lean
d423ac8511503844e93e77b2207a8a5ff593932089435808977efe26c6379c21  lean/QldpcVerification/Input/Rectangle722X12.lean
6bd9be97e12165b1a96e12d9788579019f5ab682fc1103a2e8b3530897a68ea5  lean/QldpcVerification/Input/Rectangle722X13.lean
d521065fbb75015ddcb50d9775af1f351790eecb5d3457967b43100332f23f80  lean/QldpcVerification/Input/Rectangle722X14.lean
c2c4b93dfb3f71b0ea8c868fdc3545bd4dc40c106c2f32e87723a82474901c2a  lean/QldpcVerification/Input/Rectangle722X15.lean
1637dd0c6ab4a2b98a7d5efb40b7f31e76ce84b1ac35cdb9049436d4285488cf  lean/QldpcVerification/Input/Rectangle722X16.lean
aa2f9b802a07c7dd78a90dbce4257299790e82b79fcd8aa2d87f036a78a17596  lean/QldpcVerification/Input/Rectangle722X17.lean
8e249928cde7fc991b9a2e0460731ac69f45e93862baf6dfb9a79a6f4e6f18eb  lean/QldpcVerification/Input/Rectangle722X18.lean
c9f69527ba2dad0f69bec65a96f2559e09c865effff3a8a3f5c70eeed167cb62  lean/QldpcVerification/Input/Rectangle722X19.lean
26443155cd2dfa5ef8cff5b50170e1d12bb45a6c1dd12ccb43260ace4735746c  lean/QldpcVerification/Input/Rectangle722X20.lean
7307c43bdb4523a5b9e6c238093593a356e1c8f0d430234b34f87da740dde268  lean/QldpcVerification/Input/Rectangle722Z00.lean
083e1137d224583b20078f4ba4641cbbcb526e9f429e88ecc6f3a6c13ec7a118  lean/QldpcVerification/Input/Rectangle722Z01.lean
5a4fbab56fce89215a41e79a66c279beb5cb6a5fc1182692c52e223798811a98  lean/QldpcVerification/Input/Rectangle722Z02.lean
6509c8f5b7ed75ca442bd17a3540fed7db117fa86606ee7b4d54b93c75450744  lean/QldpcVerification/Input/Rectangle722Z03.lean
6d312d30615b14f2b410bd4e5d5b9494bb0f9392e1a228fc4025da65d97cb594  lean/QldpcVerification/Input/Rectangle722Z04.lean
7586c1ce8f884ef33cc40c697c31638f4515bc22b5b2982e7d7ba9e30c7237ec  lean/QldpcVerification/Input/Rectangle722Z05.lean
f68e0310d4d8fadc1d78a5d116f7bef09ddb7136f01a57389e33ed7a115f7d3d  lean/QldpcVerification/Input/Rectangle722Z06.lean
a26934c40d2e2d1c6c57ff7ba863f16b5f2ec2c7313fc85312f38b3b3bee32c7  lean/QldpcVerification/Input/Rectangle722Z07.lean
eb0b125d9b5d03368ac7423e830c4bdec3140dd71946cd271b07d2e3654098c9  lean/QldpcVerification/Input/Rectangle722Z08.lean
40744a5f02c80f7ba5e530144b631d0ac7a4b1226adeab4393f402e3cb0ad77b  lean/QldpcVerification/Input/Rectangle722Z09.lean
31c2eb10ec556e2fe72718287ddad19a399292b134cccc156ba29cac971488a0  lean/QldpcVerification/Input/Rectangle722Z10.lean
0b2d8ed998685bf305159a79e58f567852ee143f11f9c41d82153cbee4e09fbd  lean/QldpcVerification/Input/Rectangle722Z11.lean
4795cd89b16a86ef624a35288e1f07ab56e68abcd786042c864489ae92f79ec4  lean/QldpcVerification/Input/Rectangle722Z12.lean
463b14668a703471fbedb4719f13e8c88e3816ff2c91d84cba07f70a5b152547  lean/QldpcVerification/Input/Rectangle722Z13.lean
634c05ec1186c82a7087b8a81cca6f80a75ff474f53c3c059fa5778390bed47e  lean/QldpcVerification/Input/Rectangle722Z14.lean
226ab8fc276205dbf139361d9dfaf5896558738852904df03ae875c64340b022  lean/QldpcVerification/Input/Rectangle722Z15.lean
1ef3450b701beda97fdf50ef3740a522b2330ab30de30eddd9bbc4238f55ce47  lean/QldpcVerification/Input/Rectangle722Z16.lean
-/
