def psubusw1 : instruction :=
  definst "psubusw" $ do
    pattern fun (v_3135 : reg (bv 128)) (v_3136 : reg (bv 128)) => do
      v_8893 <- getRegister v_3136;
      v_8896 <- getRegister v_3135;
      v_8899 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_8893 0 16)) (concat (expression.bv_nat 2 0) (extract v_8896 0 16)));
      v_8909 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_8893 16 32)) (concat (expression.bv_nat 2 0) (extract v_8896 16 32)));
      v_8919 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_8893 32 48)) (concat (expression.bv_nat 2 0) (extract v_8896 32 48)));
      v_8929 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_8893 48 64)) (concat (expression.bv_nat 2 0) (extract v_8896 48 64)));
      v_8939 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_8893 64 80)) (concat (expression.bv_nat 2 0) (extract v_8896 64 80)));
      v_8949 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_8893 80 96)) (concat (expression.bv_nat 2 0) (extract v_8896 80 96)));
      v_8959 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_8893 96 112)) (concat (expression.bv_nat 2 0) (extract v_8896 96 112)));
      v_8969 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_8893 112 128)) (concat (expression.bv_nat 2 0) (extract v_8896 112 128)));
      setRegister (lhs.of_reg v_3136) (concat (mux (sgt v_8899 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_8899 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_8899 2 18))) (concat (mux (sgt v_8909 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_8909 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_8909 2 18))) (concat (mux (sgt v_8919 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_8919 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_8919 2 18))) (concat (mux (sgt v_8929 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_8929 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_8929 2 18))) (concat (mux (sgt v_8939 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_8939 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_8939 2 18))) (concat (mux (sgt v_8949 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_8949 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_8949 2 18))) (concat (mux (sgt v_8959 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_8959 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_8959 2 18))) (mux (sgt v_8969 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_8969 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_8969 2 18))))))))));
      pure ()
    pat_end;
    pattern fun (v_3130 : Mem) (v_3131 : reg (bv 128)) => do
      v_15792 <- getRegister v_3131;
      v_15795 <- evaluateAddress v_3130;
      v_15796 <- load v_15795 16;
      v_15799 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_15792 0 16)) (concat (expression.bv_nat 2 0) (extract v_15796 0 16)));
      v_15809 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_15792 16 32)) (concat (expression.bv_nat 2 0) (extract v_15796 16 32)));
      v_15819 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_15792 32 48)) (concat (expression.bv_nat 2 0) (extract v_15796 32 48)));
      v_15829 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_15792 48 64)) (concat (expression.bv_nat 2 0) (extract v_15796 48 64)));
      v_15839 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_15792 64 80)) (concat (expression.bv_nat 2 0) (extract v_15796 64 80)));
      v_15849 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_15792 80 96)) (concat (expression.bv_nat 2 0) (extract v_15796 80 96)));
      v_15859 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_15792 96 112)) (concat (expression.bv_nat 2 0) (extract v_15796 96 112)));
      v_15869 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_15792 112 128)) (concat (expression.bv_nat 2 0) (extract v_15796 112 128)));
      setRegister (lhs.of_reg v_3131) (concat (mux (sgt v_15799 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_15799 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_15799 2 18))) (concat (mux (sgt v_15809 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_15809 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_15809 2 18))) (concat (mux (sgt v_15819 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_15819 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_15819 2 18))) (concat (mux (sgt v_15829 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_15829 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_15829 2 18))) (concat (mux (sgt v_15839 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_15839 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_15839 2 18))) (concat (mux (sgt v_15849 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_15849 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_15849 2 18))) (concat (mux (sgt v_15859 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_15859 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_15859 2 18))) (mux (sgt v_15869 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_15869 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_15869 2 18))))))))));
      pure ()
    pat_end
