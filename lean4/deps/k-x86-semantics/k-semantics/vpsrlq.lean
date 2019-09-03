def vpsrlq1 : instruction :=
  definst "vpsrlq" $ do
    pattern fun (v_3339 : imm int) (v_3341 : reg (bv 128)) (v_3342 : reg (bv 128)) => do
      v_8880 <- eval (concat (expression.bv_nat 56 0) (handleImmediateWithSignExtend v_3339 8 8));
      v_8882 <- getRegister v_3341;
      v_8884 <- eval (uvalueMInt v_8880);
      setRegister (lhs.of_reg v_3342) (mux (ugt v_8880 (expression.bv_nat 64 63)) (expression.bv_nat 128 0) (concat (lshr (extract v_8882 0 64) v_8884) (lshr (extract v_8882 64 128) v_8884)));
      pure ()
    pat_end;
    pattern fun (v_3351 : reg (bv 128)) (v_3352 : reg (bv 128)) (v_3353 : reg (bv 128)) => do
      v_8896 <- getRegister v_3351;
      v_8897 <- eval (extract v_8896 64 128);
      v_8899 <- getRegister v_3352;
      v_8901 <- eval (uvalueMInt v_8897);
      setRegister (lhs.of_reg v_3353) (mux (ugt v_8897 (expression.bv_nat 64 63)) (expression.bv_nat 128 0) (concat (lshr (extract v_8899 0 64) v_8901) (lshr (extract v_8899 64 128) v_8901)));
      pure ()
    pat_end;
    pattern fun (v_3356 : imm int) (v_3359 : reg (bv 256)) (v_3360 : reg (bv 256)) => do
      v_8909 <- eval (concat (expression.bv_nat 56 0) (handleImmediateWithSignExtend v_3356 8 8));
      v_8911 <- getRegister v_3359;
      v_8913 <- eval (uvalueMInt v_8909);
      setRegister (lhs.of_reg v_3360) (mux (ugt v_8909 (expression.bv_nat 64 63)) (expression.bv_nat 256 0) (concat (lshr (extract v_8911 0 64) v_8913) (concat (lshr (extract v_8911 64 128) v_8913) (concat (lshr (extract v_8911 128 192) v_8913) (lshr (extract v_8911 192 256) v_8913)))));
      pure ()
    pat_end;
    pattern fun (v_3368 : reg (bv 128)) (v_3370 : reg (bv 256)) (v_3371 : reg (bv 256)) => do
      v_8931 <- getRegister v_3368;
      v_8932 <- eval (extract v_8931 64 128);
      v_8934 <- getRegister v_3370;
      v_8936 <- eval (uvalueMInt v_8932);
      setRegister (lhs.of_reg v_3371) (mux (ugt v_8932 (expression.bv_nat 64 63)) (expression.bv_nat 256 0) (concat (lshr (extract v_8934 0 64) v_8936) (concat (lshr (extract v_8934 64 128) v_8936) (concat (lshr (extract v_8934 128 192) v_8936) (lshr (extract v_8934 192 256) v_8936)))));
      pure ()
    pat_end;
    pattern fun (v_3345 : Mem) (v_3346 : reg (bv 128)) (v_3347 : reg (bv 128)) => do
      v_14821 <- evaluateAddress v_3345;
      v_14822 <- load v_14821 16;
      v_14823 <- eval (extract v_14822 64 128);
      v_14825 <- getRegister v_3346;
      v_14827 <- eval (uvalueMInt v_14823);
      setRegister (lhs.of_reg v_3347) (mux (ugt v_14823 (expression.bv_nat 64 63)) (expression.bv_nat 128 0) (concat (lshr (extract v_14825 0 64) v_14827) (lshr (extract v_14825 64 128) v_14827)));
      pure ()
    pat_end;
    pattern fun (v_3362 : Mem) (v_3364 : reg (bv 256)) (v_3365 : reg (bv 256)) => do
      v_14834 <- evaluateAddress v_3362;
      v_14835 <- load v_14834 16;
      v_14836 <- eval (extract v_14835 64 128);
      v_14838 <- getRegister v_3364;
      v_14840 <- eval (uvalueMInt v_14836);
      setRegister (lhs.of_reg v_3365) (mux (ugt v_14836 (expression.bv_nat 64 63)) (expression.bv_nat 256 0) (concat (lshr (extract v_14838 0 64) v_14840) (concat (lshr (extract v_14838 64 128) v_14840) (concat (lshr (extract v_14838 128 192) v_14840) (lshr (extract v_14838 192 256) v_14840)))));
      pure ()
    pat_end
