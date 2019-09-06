def paddsw1 : instruction :=
  definst "paddsw" $ do
    pattern fun (v_3235 : reg (bv 128)) (v_3236 : reg (bv 128)) => do
      v_5933 <- getRegister v_3236;
      v_5936 <- getRegister v_3235;
      v_5939 <- eval (add (sext (extract v_5933 0 16) 32) (sext (extract v_5936 0 16) 32));
      v_5949 <- eval (add (sext (extract v_5933 16 32) 32) (sext (extract v_5936 16 32) 32));
      v_5959 <- eval (add (sext (extract v_5933 32 48) 32) (sext (extract v_5936 32 48) 32));
      v_5969 <- eval (add (sext (extract v_5933 48 64) 32) (sext (extract v_5936 48 64) 32));
      v_5979 <- eval (add (sext (extract v_5933 64 80) 32) (sext (extract v_5936 64 80) 32));
      v_5989 <- eval (add (sext (extract v_5933 80 96) 32) (sext (extract v_5936 80 96) 32));
      v_5999 <- eval (add (sext (extract v_5933 96 112) 32) (sext (extract v_5936 96 112) 32));
      v_6009 <- eval (add (sext (extract v_5933 112 128) 32) (sext (extract v_5936 112 128) 32));
      setRegister (lhs.of_reg v_3236) (concat (mux (sgt v_5939 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_5939 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_5939 16 32))) (concat (mux (sgt v_5949 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_5949 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_5949 16 32))) (concat (mux (sgt v_5959 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_5959 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_5959 16 32))) (concat (mux (sgt v_5969 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_5969 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_5969 16 32))) (concat (mux (sgt v_5979 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_5979 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_5979 16 32))) (concat (mux (sgt v_5989 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_5989 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_5989 16 32))) (concat (mux (sgt v_5999 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_5999 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_5999 16 32))) (mux (sgt v_6009 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_6009 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_6009 16 32))))))))));
      pure ()
    pat_end;
    pattern fun (v_3231 : Mem) (v_3232 : reg (bv 128)) => do
      v_9856 <- getRegister v_3232;
      v_9859 <- evaluateAddress v_3231;
      v_9860 <- load v_9859 16;
      v_9863 <- eval (add (sext (extract v_9856 0 16) 32) (sext (extract v_9860 0 16) 32));
      v_9873 <- eval (add (sext (extract v_9856 16 32) 32) (sext (extract v_9860 16 32) 32));
      v_9883 <- eval (add (sext (extract v_9856 32 48) 32) (sext (extract v_9860 32 48) 32));
      v_9893 <- eval (add (sext (extract v_9856 48 64) 32) (sext (extract v_9860 48 64) 32));
      v_9903 <- eval (add (sext (extract v_9856 64 80) 32) (sext (extract v_9860 64 80) 32));
      v_9913 <- eval (add (sext (extract v_9856 80 96) 32) (sext (extract v_9860 80 96) 32));
      v_9923 <- eval (add (sext (extract v_9856 96 112) 32) (sext (extract v_9860 96 112) 32));
      v_9933 <- eval (add (sext (extract v_9856 112 128) 32) (sext (extract v_9860 112 128) 32));
      setRegister (lhs.of_reg v_3232) (concat (mux (sgt v_9863 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9863 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9863 16 32))) (concat (mux (sgt v_9873 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9873 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9873 16 32))) (concat (mux (sgt v_9883 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9883 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9883 16 32))) (concat (mux (sgt v_9893 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9893 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9893 16 32))) (concat (mux (sgt v_9903 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9903 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9903 16 32))) (concat (mux (sgt v_9913 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9913 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9913 16 32))) (concat (mux (sgt v_9923 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9923 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9923 16 32))) (mux (sgt v_9933 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9933 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9933 16 32))))))))));
      pure ()
    pat_end
