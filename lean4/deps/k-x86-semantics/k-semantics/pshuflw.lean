def pshuflw1 : instruction :=
  definst "pshuflw" $ do
    pattern fun (v_3013 : imm int) (v_3014 : reg (bv 128)) (v_3015 : reg (bv 128)) => do
      v_7256 <- getRegister v_3014;
      v_7258 <- eval (handleImmediateWithSignExtend v_3013 8 8);
      setRegister (lhs.of_reg v_3015) (concat (extract v_7256 0 64) (concat (extract (lshr v_7256 (extract (shl (concat (expression.bv_nat 126 0) (extract v_7258 0 2)) (expression.bv_nat 128 4)) 0 128)) 112 128) (concat (extract (lshr v_7256 (extract (shl (concat (expression.bv_nat 126 0) (extract v_7258 2 4)) (expression.bv_nat 128 4)) 0 128)) 112 128) (concat (extract (lshr v_7256 (extract (shl (concat (expression.bv_nat 126 0) (extract v_7258 4 6)) (expression.bv_nat 128 4)) 0 128)) 112 128) (extract (lshr v_7256 (extract (shl (concat (expression.bv_nat 126 0) (extract v_7258 6 8)) (expression.bv_nat 128 4)) 0 128)) 112 128)))));
      pure ()
    pat_end;
    pattern fun (v_3009 : imm int) (v_3008 : Mem) (v_3010 : reg (bv 128)) => do
      v_13921 <- evaluateAddress v_3008;
      v_13922 <- load v_13921 16;
      v_13924 <- eval (handleImmediateWithSignExtend v_3009 8 8);
      setRegister (lhs.of_reg v_3010) (concat (extract v_13922 0 64) (concat (extract (lshr v_13922 (extract (shl (concat (expression.bv_nat 126 0) (extract v_13924 0 2)) (expression.bv_nat 128 4)) 0 128)) 112 128) (concat (extract (lshr v_13922 (extract (shl (concat (expression.bv_nat 126 0) (extract v_13924 2 4)) (expression.bv_nat 128 4)) 0 128)) 112 128) (concat (extract (lshr v_13922 (extract (shl (concat (expression.bv_nat 126 0) (extract v_13924 4 6)) (expression.bv_nat 128 4)) 0 128)) 112 128) (extract (lshr v_13922 (extract (shl (concat (expression.bv_nat 126 0) (extract v_13924 6 8)) (expression.bv_nat 128 4)) 0 128)) 112 128)))));
      pure ()
    pat_end
