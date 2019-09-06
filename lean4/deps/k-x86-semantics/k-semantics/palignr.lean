def palignr1 : instruction :=
  definst "palignr" $ do
    pattern fun (v_3272 : imm int) (v_3273 : reg (bv 128)) (v_3274 : reg (bv 128)) => do
      v_6294 <- getRegister v_3274;
      v_6295 <- getRegister v_3273;
      setRegister (lhs.of_reg v_3274) (extract (lshr (concat v_6294 v_6295) (extract (shl (concat (expression.bv_nat 248 0) (handleImmediateWithSignExtend v_3272 8 8)) (expression.bv_nat 256 3)) 0 256)) 128 256);
      pure ()
    pat_end;
    pattern fun (v_3268 : imm int) (v_3267 : Mem) (v_3269 : reg (bv 128)) => do
      v_10204 <- getRegister v_3269;
      v_10205 <- evaluateAddress v_3267;
      v_10206 <- load v_10205 16;
      setRegister (lhs.of_reg v_3269) (extract (lshr (concat v_10204 v_10206) (extract (shl (concat (expression.bv_nat 248 0) (handleImmediateWithSignExtend v_3268 8 8)) (expression.bv_nat 256 3)) 0 256)) 128 256);
      pure ()
    pat_end
