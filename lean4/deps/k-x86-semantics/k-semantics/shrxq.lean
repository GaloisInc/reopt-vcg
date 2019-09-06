def shrxq1 : instruction :=
  definst "shrxq" $ do
    pattern fun (v_3116 : reg (bv 64)) (v_3117 : reg (bv 64)) (v_3118 : reg (bv 64)) => do
      v_5403 <- getRegister v_3117;
      v_5405 <- getRegister v_3116;
      setRegister (lhs.of_reg v_3118) (extract (lshr (concat v_5403 (expression.bv_nat 1 0)) (concat (expression.bv_nat 57 0) (bv_and (extract v_5405 56 64) (expression.bv_nat 8 63)))) 0 64);
      pure ()
    pat_end;
    pattern fun (v_3107 : reg (bv 64)) (v_3106 : Mem) (v_3108 : reg (bv 64)) => do
      v_8477 <- evaluateAddress v_3106;
      v_8478 <- load v_8477 8;
      v_8480 <- getRegister v_3107;
      setRegister (lhs.of_reg v_3108) (extract (lshr (concat v_8478 (expression.bv_nat 1 0)) (concat (expression.bv_nat 57 0) (bv_and (extract v_8480 56 64) (expression.bv_nat 8 63)))) 0 64);
      pure ()
    pat_end
