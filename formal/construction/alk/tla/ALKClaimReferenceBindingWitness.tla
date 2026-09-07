---- MODULE ALKClaimReferenceBindingWitness ----
EXTENDS ALKReferenceClaimView

VARIABLE certificateFault
certificateVars == <<vars, certificateFault>>
CertificateInit == Init /\ certificateFault = "none"
\* Explore the original relation so the gate-equivalence property cannot
\* pass by removing an original transition from the tested behavior.
CertificateNext == Next /\ UNCHANGED certificateFault
CertificateSpec == CertificateInit /\ [][CertificateNext]_certificateVars

CandidateReferenceResult ==
    CASE certificateFault = "wrong-profile" ->
           [ReferenceResult EXCEPT !.certificate =
               ClaimCertificate!StaticClaimCertificate("delegated", AssuranceMode, configVersion)]
      [] certificateFault = "wrong-revision" ->
           [ReferenceResult EXCEPT !.certificate =
               ClaimCertificate!StaticClaimCertificate(Profile, AssuranceMode, 2)]
      [] certificateFault = "wrong-issuer" ->
           [ReferenceResult EXCEPT !.claims["reference-effect-count"].issuer = configuredOwner]
      [] certificateFault = "wrong-predicate" ->
           [ReferenceResult EXCEPT !.claims["reference-effect-count"].predicate =
               "ALKReferenceStateMachine!SuccessCoupled"]
      [] certificateFault = "kind-as-obligation" ->
           [ReferenceResult EXCEPT !.claims["reference-effect-count"].frame.obligation = "prevention"]
      [] certificateFault = "missing-residuals" ->
           [ReferenceResult EXCEPT !.residuals = {}]
      [] certificateFault = "false-truth" ->
           [ReferenceResult EXCEPT !.claims["reference-effect-count"].outcome = "holds"]
      [] OTHER -> ReferenceResult

CandidateCertificateHeld ==
    /\ CandidateReferenceResult.certificate = ConfiguredClaimCertificate
    /\ CandidateReferenceResult.claims = ReferenceClaimResults
    /\ CandidateReferenceResult.residuals = ReferenceResult.residuals
ReferenceGateBinding ==
    [][Next => CertifiedNext]_vars
CertificateInvariant == ReferenceClaimViewInvariant /\ CandidateCertificateHeld
====
