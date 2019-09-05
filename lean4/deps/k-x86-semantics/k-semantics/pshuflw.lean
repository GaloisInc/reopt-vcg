def pshuflw1 : instruction :=
  definst "pshuflw" $ do
    pattern fun (v_2987 : imm int) (v_2985 : reg (bv 128)) (v_2986 : reg (bv 128)) => do
      v_7229 <- getRegister v_2985;
      v_7231 <- eval (handleImmediateWithSignExtend v_2987 8 8);
      setRegister (lhs.of_reg v_2986) (concat (extract v_7229 0 64) (concat (extract (lshr v_7229 (extract (shl (concat (expression.bv_nat 126 0) (extract v_7231 0 2)) (expression.bv_nat 128 4)) 0 128)) 112 128) (concat (extract (lshr v_7229 (extract (shl (concat (expression.bv_nat 126 0) (extract v_7231 2 4)) (expression.bv_nat 128 4)) 0 128)) 112 128) (concat (extract (lshr v_7229 (extract (shl (concat (expression.bv_nat 126 0) (extract v_7231 4 6)) (expression.bv_nat 128 4)) 0 128)) 112 128) (extract (lshr v_7229 (extract (shl (concat (expression.bv_nat 126 0) (extract v_7231 6 8)) (expression.bv_nat 128 4)) 0 128)) 112 128)))));
      pure ()
    pat_end;
    pattern fun (v_2981 : imm int) (v_2982 : Mem) (v_2980 : reg (bv 128)) => do
      v_13945 <- evaluateAddress v_2982;
      v_13946 <- load v_13945 16;
      v_13948 <- eval (handleImmediateWithSignExtend v_2981 8 8);
      setRegister (lhs.of_reg v_2980) (concat (extract v_13946 0 64) (concat (extract (lshr v_13946 (extract (shl (concat (expression.bv_nat 126 0) (extract v_13948 0 2)) (expression.bv_nat 128 4)) 0 128)) 112 128) (concat (extract (lshr v_13946 (extract (shl (concat (expression.bv_nat 126 0) (extract v_13948 2 4)) (expression.bv_nat 128 4)) 0 128)) 112 128) (concat (extract (lshr v_13946 (extract (shl (concat (expression.bv_nat 126 0) (extract v_13948 4 6)) (expression.bv_nat 128 4)) 0 128)) 112 128) (extract (lshr v_13946 (extract (shl (concat (expression.bv_nat 126 0) (extract v_13948 6 8)) (expression.bv_nat 128 4)) 0 128)) 112 128)))));
      pure ()
    pat_end
