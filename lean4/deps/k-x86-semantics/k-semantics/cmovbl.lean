def cmovbl1 : instruction :=
  definst "cmovbl" $ do
    pattern fun (v_2491 : reg (bv 32)) (v_2492 : reg (bv 32)) => do
      v_4171 <- getRegister cf;
      v_4173 <- getRegister v_2491;
      v_4174 <- getRegister v_2492;
      setRegister (lhs.of_reg v_2492) (mux (eq v_4171 (expression.bv_nat 1 1)) v_4173 v_4174);
      pure ()
    pat_end;
    pattern fun (v_2487 : Mem) (v_2488 : reg (bv 32)) => do
      v_7866 <- getRegister cf;
      v_7868 <- evaluateAddress v_2487;
      v_7869 <- load v_7868 4;
      v_7870 <- getRegister v_2488;
      setRegister (lhs.of_reg v_2488) (mux (eq v_7866 (expression.bv_nat 1 1)) v_7869 v_7870);
      pure ()
    pat_end
