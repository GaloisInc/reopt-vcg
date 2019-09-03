def cmovew1 : instruction :=
  definst "cmovew" $ do
    pattern fun (v_2551 : reg (bv 16)) (v_2552 : reg (bv 16)) => do
      v_4238 <- getRegister zf;
      v_4240 <- getRegister v_2551;
      v_4241 <- getRegister v_2552;
      setRegister (lhs.of_reg v_2552) (mux (eq v_4238 (expression.bv_nat 1 1)) v_4240 v_4241);
      pure ()
    pat_end;
    pattern fun (v_2548 : Mem) (v_2547 : reg (bv 16)) => do
      v_7949 <- getRegister zf;
      v_7951 <- evaluateAddress v_2548;
      v_7952 <- load v_7951 2;
      v_7953 <- getRegister v_2547;
      setRegister (lhs.of_reg v_2547) (mux (eq v_7949 (expression.bv_nat 1 1)) v_7952 v_7953);
      pure ()
    pat_end
