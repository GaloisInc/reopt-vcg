def andnps1 : instruction :=
  definst "andnps" $ do
    pattern fun (v_2867 : reg (bv 128)) (v_2868 : reg (bv 128)) => do
      v_5385 <- getRegister v_2868;
      v_5387 <- getRegister v_2867;
      setRegister (lhs.of_reg v_2868) (bv_and (bv_xor v_5385 (expression.bv_nat 128 340282366920938463463374607431768211455)) v_5387);
      pure ()
    pat_end;
    pattern fun (v_2862 : Mem) (v_2863 : reg (bv 128)) => do
      v_9172 <- getRegister v_2863;
      v_9174 <- evaluateAddress v_2862;
      v_9175 <- load v_9174 16;
      setRegister (lhs.of_reg v_2863) (bv_and (bv_xor v_9172 (expression.bv_nat 128 340282366920938463463374607431768211455)) v_9175);
      pure ()
    pat_end
