def cmovzw1 : instruction :=
  definst "cmovzw" $ do
    pattern fun (v_3295 : reg (bv 16)) (v_3296 : reg (bv 16)) => do
      v_5192 <- getRegister zf;
      v_5194 <- getRegister v_3295;
      v_5195 <- getRegister v_3296;
      setRegister (lhs.of_reg v_3296) (mux (eq v_5192 (expression.bv_nat 1 1)) v_5194 v_5195);
      pure ()
    pat_end;
    pattern fun (v_3292 : Mem) (v_3291 : reg (bv 16)) => do
      v_8639 <- getRegister zf;
      v_8641 <- evaluateAddress v_3292;
      v_8642 <- load v_8641 2;
      v_8643 <- getRegister v_3291;
      setRegister (lhs.of_reg v_3291) (mux (eq v_8639 (expression.bv_nat 1 1)) v_8642 v_8643);
      pure ()
    pat_end
