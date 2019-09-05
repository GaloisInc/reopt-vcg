def psubsw1 : instruction :=
  definst "psubsw" $ do
    pattern fun (v_3180 : reg (bv 128)) (v_3181 : reg (bv 128)) => do
      v_8234 <- getRegister v_3181;
      v_8237 <- getRegister v_3180;
      v_8240 <- eval (sub (sext (extract v_8234 0 16) 18) (sext (extract v_8237 0 16) 18));
      v_8250 <- eval (sub (sext (extract v_8234 16 32) 18) (sext (extract v_8237 16 32) 18));
      v_8260 <- eval (sub (sext (extract v_8234 32 48) 18) (sext (extract v_8237 32 48) 18));
      v_8270 <- eval (sub (sext (extract v_8234 48 64) 18) (sext (extract v_8237 48 64) 18));
      v_8280 <- eval (sub (sext (extract v_8234 64 80) 18) (sext (extract v_8237 64 80) 18));
      v_8290 <- eval (sub (sext (extract v_8234 80 96) 18) (sext (extract v_8237 80 96) 18));
      v_8300 <- eval (sub (sext (extract v_8234 96 112) 18) (sext (extract v_8237 96 112) 18));
      v_8310 <- eval (sub (sext (extract v_8234 112 128) 18) (sext (extract v_8237 112 128) 18));
      setRegister (lhs.of_reg v_3181) (concat (mux (sgt v_8240 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_8240 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_8240 2 18))) (concat (mux (sgt v_8250 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_8250 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_8250 2 18))) (concat (mux (sgt v_8260 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_8260 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_8260 2 18))) (concat (mux (sgt v_8270 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_8270 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_8270 2 18))) (concat (mux (sgt v_8280 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_8280 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_8280 2 18))) (concat (mux (sgt v_8290 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_8290 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_8290 2 18))) (concat (mux (sgt v_8300 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_8300 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_8300 2 18))) (mux (sgt v_8310 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_8310 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_8310 2 18))))))))));
      pure ()
    pat_end;
    pattern fun (v_3177 : Mem) (v_3176 : reg (bv 128)) => do
      v_14703 <- getRegister v_3176;
      v_14706 <- evaluateAddress v_3177;
      v_14707 <- load v_14706 16;
      v_14710 <- eval (sub (sext (extract v_14703 0 16) 18) (sext (extract v_14707 0 16) 18));
      v_14720 <- eval (sub (sext (extract v_14703 16 32) 18) (sext (extract v_14707 16 32) 18));
      v_14730 <- eval (sub (sext (extract v_14703 32 48) 18) (sext (extract v_14707 32 48) 18));
      v_14740 <- eval (sub (sext (extract v_14703 48 64) 18) (sext (extract v_14707 48 64) 18));
      v_14750 <- eval (sub (sext (extract v_14703 64 80) 18) (sext (extract v_14707 64 80) 18));
      v_14760 <- eval (sub (sext (extract v_14703 80 96) 18) (sext (extract v_14707 80 96) 18));
      v_14770 <- eval (sub (sext (extract v_14703 96 112) 18) (sext (extract v_14707 96 112) 18));
      v_14780 <- eval (sub (sext (extract v_14703 112 128) 18) (sext (extract v_14707 112 128) 18));
      setRegister (lhs.of_reg v_3176) (concat (mux (sgt v_14710 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_14710 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_14710 2 18))) (concat (mux (sgt v_14720 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_14720 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_14720 2 18))) (concat (mux (sgt v_14730 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_14730 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_14730 2 18))) (concat (mux (sgt v_14740 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_14740 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_14740 2 18))) (concat (mux (sgt v_14750 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_14750 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_14750 2 18))) (concat (mux (sgt v_14760 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_14760 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_14760 2 18))) (concat (mux (sgt v_14770 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_14770 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_14770 2 18))) (mux (sgt v_14780 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_14780 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_14780 2 18))))))))));
      pure ()
    pat_end
