def vpextrw1 : instruction :=
  definst "vpextrw" $ do
    pattern fun (v_3223 : imm int) (v_3224 : reg (bv 128)) (v_3225 : reg (bv 32)) => do
      v_8665 <- getRegister v_3224;
      setRegister (lhs.of_reg v_3225) (concat (expression.bv_nat 16 0) (extract (lshr v_8665 (extract (shl (concat (expression.bv_nat 125 0) (extract (handleImmediateWithSignExtend v_3223 8 8) 5 8)) (expression.bv_nat 128 4)) 0 128)) 112 128));
      pure ()
    pat_end;
    pattern fun (v_3229 : imm int) (v_3230 : reg (bv 128)) (v_3232 : reg (bv 64)) => do
      v_8675 <- getRegister v_3230;
      setRegister (lhs.of_reg v_3232) (concat (expression.bv_nat 48 0) (extract (lshr v_8675 (extract (shl (concat (expression.bv_nat 125 0) (extract (handleImmediateWithSignExtend v_3229 8 8) 5 8)) (expression.bv_nat 128 4)) 0 128)) 112 128));
      pure ()
    pat_end;
    pattern fun (v_3219 : imm int) (v_3220 : reg (bv 128)) (v_3218 : Mem) => do
      v_19235 <- evaluateAddress v_3218;
      v_19236 <- getRegister v_3220;
      store v_19235 (extract (lshr v_19236 (extract (shl (concat (expression.bv_nat 125 0) (extract (handleImmediateWithSignExtend v_3219 8 8) 5 8)) (expression.bv_nat 128 4)) 0 128)) 112 128) 2;
      pure ()
    pat_end
