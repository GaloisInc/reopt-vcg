def vshufpd1 : instruction :=
  definst "vshufpd" $ do
    pattern fun (v_2917 : imm int) (v_2918 : reg (bv 128)) (v_2919 : reg (bv 128)) (v_2920 : reg (bv 128)) => do
      v_6880 <- eval (handleImmediateWithSignExtend v_2917 8 8);
      v_6883 <- getRegister v_2918;
      v_6889 <- getRegister v_2919;
      setRegister (lhs.of_reg v_2920) (concat (mux (eq (extract v_6880 6 7) (expression.bv_nat 1 1)) (extract v_6883 0 64) (extract v_6883 64 128)) (mux (eq (extract v_6880 7 8) (expression.bv_nat 1 1)) (extract v_6889 0 64) (extract v_6889 64 128)));
      pure ()
    pat_end;
    pattern fun (v_2930 : imm int) (v_2931 : reg (bv 256)) (v_2932 : reg (bv 256)) (v_2933 : reg (bv 256)) => do
      v_6901 <- eval (handleImmediateWithSignExtend v_2930 8 8);
      v_6904 <- getRegister v_2931;
      v_6910 <- getRegister v_2932;
      setRegister (lhs.of_reg v_2933) (concat (mux (eq (extract v_6901 4 5) (expression.bv_nat 1 1)) (extract v_6904 0 64) (extract v_6904 64 128)) (concat (mux (eq (extract v_6901 5 6) (expression.bv_nat 1 1)) (extract v_6910 0 64) (extract v_6910 64 128)) (concat (mux (eq (extract v_6901 6 7) (expression.bv_nat 1 1)) (extract v_6904 128 192) (extract v_6904 192 256)) (mux (eq (extract v_6901 7 8) (expression.bv_nat 1 1)) (extract v_6910 128 192) (extract v_6910 192 256)))));
      pure ()
    pat_end;
    pattern fun (v_2911 : imm int) (v_2912 : Mem) (v_2913 : reg (bv 128)) (v_2914 : reg (bv 128)) => do
      v_13220 <- eval (handleImmediateWithSignExtend v_2911 8 8);
      v_13223 <- evaluateAddress v_2912;
      v_13224 <- load v_13223 16;
      v_13230 <- getRegister v_2913;
      setRegister (lhs.of_reg v_2914) (concat (mux (eq (extract v_13220 6 7) (expression.bv_nat 1 1)) (extract v_13224 0 64) (extract v_13224 64 128)) (mux (eq (extract v_13220 7 8) (expression.bv_nat 1 1)) (extract v_13230 0 64) (extract v_13230 64 128)));
      pure ()
    pat_end;
    pattern fun (v_2924 : imm int) (v_2925 : Mem) (v_2926 : reg (bv 256)) (v_2927 : reg (bv 256)) => do
      v_13236 <- eval (handleImmediateWithSignExtend v_2924 8 8);
      v_13239 <- evaluateAddress v_2925;
      v_13240 <- load v_13239 32;
      v_13246 <- getRegister v_2926;
      setRegister (lhs.of_reg v_2927) (concat (mux (eq (extract v_13236 4 5) (expression.bv_nat 1 1)) (extract v_13240 0 64) (extract v_13240 64 128)) (concat (mux (eq (extract v_13236 5 6) (expression.bv_nat 1 1)) (extract v_13246 0 64) (extract v_13246 64 128)) (concat (mux (eq (extract v_13236 6 7) (expression.bv_nat 1 1)) (extract v_13240 128 192) (extract v_13240 192 256)) (mux (eq (extract v_13236 7 8) (expression.bv_nat 1 1)) (extract v_13246 128 192) (extract v_13246 192 256)))));
      pure ()
    pat_end
