def vpermpd1 : instruction :=
  definst "vpermpd" $ do
    pattern fun (v_3151 : imm int) (v_3152 : reg (bv 256)) (v_3153 : reg (bv 256)) => do
      v_8487 <- getRegister v_3152;
      v_8488 <- eval (handleImmediateWithSignExtend v_3151 8 8);
      setRegister (lhs.of_reg v_3153) (concat (extract (lshr v_8487 (extract (shl (concat (expression.bv_nat 254 0) (extract v_8488 0 2)) (expression.bv_nat 256 6)) 0 256)) 192 256) (concat (extract (lshr v_8487 (extract (shl (concat (expression.bv_nat 254 0) (extract v_8488 2 4)) (expression.bv_nat 256 6)) 0 256)) 192 256) (concat (extract (lshr v_8487 (extract (shl (concat (expression.bv_nat 254 0) (extract v_8488 4 6)) (expression.bv_nat 256 6)) 0 256)) 192 256) (extract (lshr v_8487 (extract (shl (concat (expression.bv_nat 254 0) (extract v_8488 6 8)) (expression.bv_nat 256 6)) 0 256)) 192 256))));
      pure ()
    pat_end;
    pattern fun (v_3147 : imm int) (v_3146 : Mem) (v_3148 : reg (bv 256)) => do
      v_16993 <- evaluateAddress v_3146;
      v_16994 <- load v_16993 32;
      v_16995 <- eval (handleImmediateWithSignExtend v_3147 8 8);
      setRegister (lhs.of_reg v_3148) (concat (extract (lshr v_16994 (extract (shl (concat (expression.bv_nat 254 0) (extract v_16995 0 2)) (expression.bv_nat 256 6)) 0 256)) 192 256) (concat (extract (lshr v_16994 (extract (shl (concat (expression.bv_nat 254 0) (extract v_16995 2 4)) (expression.bv_nat 256 6)) 0 256)) 192 256) (concat (extract (lshr v_16994 (extract (shl (concat (expression.bv_nat 254 0) (extract v_16995 4 6)) (expression.bv_nat 256 6)) 0 256)) 192 256) (extract (lshr v_16994 (extract (shl (concat (expression.bv_nat 254 0) (extract v_16995 6 8)) (expression.bv_nat 256 6)) 0 256)) 192 256))));
      pure ()
    pat_end
