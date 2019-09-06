def cmovle1 : instruction :=
  definst "cmovle" $ do
    pattern fun (v_2724 : Mem) (v_2727 : reg (bv 32)) => do
      v_8699 <- getRegister zf;
      v_8700 <- getRegister sf;
      v_8701 <- getRegister of;
      v_8705 <- evaluateAddress v_2724;
      v_8706 <- load v_8705 4;
      v_8707 <- getRegister v_2727;
      setRegister (lhs.of_reg v_2727) (mux (bit_or v_8699 (notBool_ (eq v_8700 v_8701))) v_8706 v_8707);
      pure ()
    pat_end;
    pattern fun (v_2742 : Mem) (v_2741 : reg (bv 64)) => do
      v_8710 <- getRegister zf;
      v_8711 <- getRegister sf;
      v_8712 <- getRegister of;
      v_8716 <- evaluateAddress v_2742;
      v_8717 <- load v_8716 8;
      v_8718 <- getRegister v_2741;
      setRegister (lhs.of_reg v_2741) (mux (bit_or v_8710 (notBool_ (eq v_8711 v_8712))) v_8717 v_8718);
      pure ()
    pat_end;
    pattern fun (v_2758 : Mem) (v_2759 : reg (bv 16)) => do
      v_8721 <- getRegister zf;
      v_8722 <- getRegister sf;
      v_8723 <- getRegister of;
      v_8727 <- evaluateAddress v_2758;
      v_8728 <- load v_8727 2;
      v_8729 <- getRegister v_2759;
      setRegister (lhs.of_reg v_2759) (mux (bit_or v_8721 (notBool_ (eq v_8722 v_8723))) v_8728 v_8729);
      pure ()
    pat_end
