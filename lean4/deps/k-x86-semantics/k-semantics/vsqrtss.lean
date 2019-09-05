def vsqrtss1 : instruction :=
  definst "vsqrtss" $ do
    pattern fun (v_3069 : reg (bv 128)) (v_3070 : reg (bv 128)) (v_3071 : reg (bv 128)) => do
      v_7090 <- getRegister v_3070;
      v_7092 <- getRegister v_3069;
      setRegister (lhs.of_reg v_3071) (concat (extract v_7090 0 96) (_(_)_MINT-WRAPPER-SYNTAX sqrt_single (extract v_7092 96 128)));
      pure ()
    pat_end;
    pattern fun (v_3063 : Mem) (v_3064 : reg (bv 128)) (v_3065 : reg (bv 128)) => do
      v_13021 <- getRegister v_3064;
      v_13023 <- evaluateAddress v_3063;
      v_13024 <- load v_13023 4;
      setRegister (lhs.of_reg v_3065) (concat (extract v_13021 0 96) (_(_)_MINT-WRAPPER-SYNTAX sqrt_single v_13024));
      pure ()
    pat_end
