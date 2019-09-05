def shrxq1 : instruction :=
  definst "shrxq" $ do
    pattern fun (v_3089 : reg (bv 64)) (v_3090 : reg (bv 64)) (v_3091 : reg (bv 64)) => do
      v_5948 <- getRegister v_3090;
      v_5950 <- getRegister v_3089;
      setRegister (lhs.of_reg v_3091) (extract (lshr (concat v_5948 (expression.bv_nat 1 0)) (concat (expression.bv_nat 57 0) (bv_and (extract v_5950 56 64) (expression.bv_nat 8 63)))) 0 64);
      pure ()
    pat_end;
    pattern fun (v_3079 : reg (bv 64)) (v_3078 : Mem) (v_3080 : reg (bv 64)) => do
      v_9084 <- evaluateAddress v_3078;
      v_9085 <- load v_9084 8;
      v_9087 <- getRegister v_3079;
      setRegister (lhs.of_reg v_3080) (extract (lshr (concat v_9085 (expression.bv_nat 1 0)) (concat (expression.bv_nat 57 0) (bv_and (extract v_9087 56 64) (expression.bv_nat 8 63)))) 0 64);
      pure ()
    pat_end
