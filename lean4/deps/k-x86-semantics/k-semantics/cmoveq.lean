def cmoveq1 : instruction :=
  definst "cmoveq" $ do
    pattern fun (v_2543 : reg (bv 64)) (v_2544 : reg (bv 64)) => do
      v_4228 <- getRegister zf;
      v_4230 <- getRegister v_2543;
      v_4231 <- getRegister v_2544;
      setRegister (lhs.of_reg v_2544) (mux (eq v_4228 (expression.bv_nat 1 1)) v_4230 v_4231);
      pure ()
    pat_end;
    pattern fun (v_2538 : Mem) (v_2539 : reg (bv 64)) => do
      v_7942 <- getRegister zf;
      v_7944 <- evaluateAddress v_2538;
      v_7945 <- load v_7944 8;
      v_7946 <- getRegister v_2539;
      setRegister (lhs.of_reg v_2539) (mux (eq v_7942 (expression.bv_nat 1 1)) v_7945 v_7946);
      pure ()
    pat_end
