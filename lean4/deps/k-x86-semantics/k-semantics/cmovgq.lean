def cmovgq1 : instruction :=
  definst "cmovgq" $ do
    pattern fun (v_2710 : reg (bv 64)) (v_2711 : reg (bv 64)) => do
      v_4378 <- getRegister zf;
      v_4380 <- getRegister sf;
      v_4381 <- getRegister of;
      v_4384 <- getRegister v_2710;
      v_4385 <- getRegister v_2711;
      setRegister (lhs.of_reg v_2711) (mux (bit_and (notBool_ v_4378) (eq v_4380 v_4381)) v_4384 v_4385);
      pure ()
    pat_end;
    pattern fun (v_2706 : Mem) (v_2707 : reg (bv 64)) => do
      v_7810 <- getRegister zf;
      v_7812 <- getRegister sf;
      v_7813 <- getRegister of;
      v_7816 <- evaluateAddress v_2706;
      v_7817 <- load v_7816 8;
      v_7818 <- getRegister v_2707;
      setRegister (lhs.of_reg v_2707) (mux (bit_and (notBool_ v_7810) (eq v_7812 v_7813)) v_7817 v_7818);
      pure ()
    pat_end
