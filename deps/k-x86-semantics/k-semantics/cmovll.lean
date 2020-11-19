def cmovll : instruction :=
  definst "cmovll" $ do
    pattern fun (mem_0 : Mem) (r32_1 : reg (bv 32)) => do
      v_2 <- getRegister sf;
      v_3 <- getRegister of;
      v_4 <- evaluateAddress mem_0;
      v_5 <- load v_4 4;
      v_6 <- getRegister (lhs.of_reg r32_1);
      setRegister (lhs.of_reg r32_1) (mux (notBool_ (eq v_2 v_3)) v_5 v_6);
      pure ()
    pat_end;
    pattern fun (r32_0 : reg (bv 32)) (r32_1 : reg (bv 32)) => do
      v_2 <- getRegister sf;
      v_3 <- getRegister of;
      v_4 <- getRegister (lhs.of_reg r32_0);
      v_5 <- getRegister (lhs.of_reg r32_1);
      setRegister (lhs.of_reg r32_1) (mux (notBool_ (eq v_2 v_3)) v_4 v_5);
      pure ()
    pat_end
