def sqrtsd1 : instruction :=
  definst "sqrtsd" $ do
    pattern fun (v_3138 : reg (bv 128)) (v_3139 : reg (bv 128)) => do
      v_6047 <- getRegister v_3139;
      v_6049 <- getRegister v_3138;
      setRegister (lhs.of_reg v_3139) (concat (extract v_6047 0 64) (_(_)_MINT-WRAPPER-SYNTAX sqrt_double (extract v_6049 64 128)));
      pure ()
    pat_end;
    pattern fun (v_3135 : Mem) (v_3134 : reg (bv 128)) => do
      v_9166 <- getRegister v_3134;
      v_9168 <- evaluateAddress v_3135;
      v_9169 <- load v_9168 8;
      setRegister (lhs.of_reg v_3134) (concat (extract v_9166 0 64) (_(_)_MINT-WRAPPER-SYNTAX sqrt_double v_9169));
      pure ()
    pat_end
