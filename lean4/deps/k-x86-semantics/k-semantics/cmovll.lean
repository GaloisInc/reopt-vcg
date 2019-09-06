def cmovll1 : instruction :=
  definst "cmovll" $ do
    pattern fun (v_2782 : reg (bv 32)) (v_2783 : reg (bv 32)) => do
      v_4463 <- getRegister sf;
      v_4464 <- getRegister of;
      v_4467 <- getRegister v_2782;
      v_4468 <- getRegister v_2783;
      setRegister (lhs.of_reg v_2783) (mux (notBool_ (eq v_4463 v_4464)) v_4467 v_4468);
      pure ()
    pat_end;
    pattern fun (v_2775 : Mem) (v_2778 : reg (bv 32)) => do
      v_7868 <- getRegister sf;
      v_7869 <- getRegister of;
      v_7872 <- evaluateAddress v_2775;
      v_7873 <- load v_7872 4;
      v_7874 <- getRegister v_2778;
      setRegister (lhs.of_reg v_2778) (mux (notBool_ (eq v_7868 v_7869)) v_7873 v_7874);
      pure ()
    pat_end
