def palignr1 : instruction :=
  definst "palignr" $ do
    pattern fun (v_3246 : imm int) (v_3248 : reg (bv 128)) (v_3249 : reg (bv 128)) => do
      v_6267 <- getRegister v_3249;
      v_6268 <- getRegister v_3248;
      setRegister (lhs.of_reg v_3249) (extract (lshr (concat v_6267 v_6268) (extract (shl (concat (expression.bv_nat 248 0) (handleImmediateWithSignExtend v_3246 8 8)) (expression.bv_nat 256 3)) 0 256)) 128 256);
      pure ()
    pat_end;
    pattern fun (v_3241 : imm int) (v_3242 : Mem) (v_3243 : reg (bv 128)) => do
      v_10177 <- getRegister v_3243;
      v_10178 <- evaluateAddress v_3242;
      v_10179 <- load v_10178 16;
      setRegister (lhs.of_reg v_3243) (extract (lshr (concat v_10177 v_10179) (extract (shl (concat (expression.bv_nat 248 0) (handleImmediateWithSignExtend v_3241 8 8)) (expression.bv_nat 256 3)) 0 256)) 128 256);
      pure ()
    pat_end
