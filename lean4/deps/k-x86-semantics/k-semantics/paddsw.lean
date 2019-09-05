def paddsw1 : instruction :=
  definst "paddsw" $ do
    pattern fun (v_3210 : reg (bv 128)) (v_3211 : reg (bv 128)) => do
      v_5906 <- getRegister v_3211;
      v_5909 <- getRegister v_3210;
      v_5912 <- eval (add (sext (extract v_5906 0 16) 32) (sext (extract v_5909 0 16) 32));
      v_5922 <- eval (add (sext (extract v_5906 16 32) 32) (sext (extract v_5909 16 32) 32));
      v_5932 <- eval (add (sext (extract v_5906 32 48) 32) (sext (extract v_5909 32 48) 32));
      v_5942 <- eval (add (sext (extract v_5906 48 64) 32) (sext (extract v_5909 48 64) 32));
      v_5952 <- eval (add (sext (extract v_5906 64 80) 32) (sext (extract v_5909 64 80) 32));
      v_5962 <- eval (add (sext (extract v_5906 80 96) 32) (sext (extract v_5909 80 96) 32));
      v_5972 <- eval (add (sext (extract v_5906 96 112) 32) (sext (extract v_5909 96 112) 32));
      v_5982 <- eval (add (sext (extract v_5906 112 128) 32) (sext (extract v_5909 112 128) 32));
      setRegister (lhs.of_reg v_3211) (concat (mux (sgt v_5912 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_5912 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_5912 16 32))) (concat (mux (sgt v_5922 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_5922 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_5922 16 32))) (concat (mux (sgt v_5932 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_5932 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_5932 16 32))) (concat (mux (sgt v_5942 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_5942 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_5942 16 32))) (concat (mux (sgt v_5952 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_5952 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_5952 16 32))) (concat (mux (sgt v_5962 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_5962 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_5962 16 32))) (concat (mux (sgt v_5972 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_5972 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_5972 16 32))) (mux (sgt v_5982 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_5982 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_5982 16 32))))))))));
      pure ()
    pat_end;
    pattern fun (v_3205 : Mem) (v_3206 : reg (bv 128)) => do
      v_9829 <- getRegister v_3206;
      v_9832 <- evaluateAddress v_3205;
      v_9833 <- load v_9832 16;
      v_9836 <- eval (add (sext (extract v_9829 0 16) 32) (sext (extract v_9833 0 16) 32));
      v_9846 <- eval (add (sext (extract v_9829 16 32) 32) (sext (extract v_9833 16 32) 32));
      v_9856 <- eval (add (sext (extract v_9829 32 48) 32) (sext (extract v_9833 32 48) 32));
      v_9866 <- eval (add (sext (extract v_9829 48 64) 32) (sext (extract v_9833 48 64) 32));
      v_9876 <- eval (add (sext (extract v_9829 64 80) 32) (sext (extract v_9833 64 80) 32));
      v_9886 <- eval (add (sext (extract v_9829 80 96) 32) (sext (extract v_9833 80 96) 32));
      v_9896 <- eval (add (sext (extract v_9829 96 112) 32) (sext (extract v_9833 96 112) 32));
      v_9906 <- eval (add (sext (extract v_9829 112 128) 32) (sext (extract v_9833 112 128) 32));
      setRegister (lhs.of_reg v_3206) (concat (mux (sgt v_9836 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9836 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9836 16 32))) (concat (mux (sgt v_9846 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9846 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9846 16 32))) (concat (mux (sgt v_9856 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9856 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9856 16 32))) (concat (mux (sgt v_9866 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9866 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9866 16 32))) (concat (mux (sgt v_9876 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9876 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9876 16 32))) (concat (mux (sgt v_9886 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9886 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9886 16 32))) (concat (mux (sgt v_9896 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9896 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9896 16 32))) (mux (sgt v_9906 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9906 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9906 16 32))))))))));
      pure ()
    pat_end
