def vsqrtss1 : instruction :=
  definst "vsqrtss" $ do
    pattern fun (v_3096 : reg (bv 128)) (v_3097 : reg (bv 128)) (v_3098 : reg (bv 128)) => do
      v_7117 <- getRegister v_3097;
      v_7119 <- getRegister v_3096;
      setRegister (lhs.of_reg v_3098) (concat (extract v_7117 0 96) (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_7119 96 128)));
      pure ()
    pat_end;
    pattern fun (v_3090 : Mem) (v_3091 : reg (bv 128)) (v_3092 : reg (bv 128)) => do
      v_13048 <- getRegister v_3091;
      v_13050 <- evaluateAddress v_3090;
      v_13051 <- load v_13050 4;
      setRegister (lhs.of_reg v_3092) (concat (extract v_13048 0 96) (_(_)_MINT-WRAPPER-SYNTAX sqrt_single v_13051));
      pure ()
    pat_end
