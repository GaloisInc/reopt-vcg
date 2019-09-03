def paddsw1 : instruction :=
  definst "paddsw" $ do
    pattern fun (v_3159 : reg (bv 128)) (v_3160 : reg (bv 128)) => do
      v_5993 <- getRegister v_3160;
      v_5996 <- getRegister v_3159;
      v_5999 <- eval (add (leanSignExtend (extract v_5993 0 16) 32) (leanSignExtend (extract v_5996 0 16) 32));
      v_6009 <- eval (add (leanSignExtend (extract v_5993 16 32) 32) (leanSignExtend (extract v_5996 16 32) 32));
      v_6019 <- eval (add (leanSignExtend (extract v_5993 32 48) 32) (leanSignExtend (extract v_5996 32 48) 32));
      v_6029 <- eval (add (leanSignExtend (extract v_5993 48 64) 32) (leanSignExtend (extract v_5996 48 64) 32));
      v_6039 <- eval (add (leanSignExtend (extract v_5993 64 80) 32) (leanSignExtend (extract v_5996 64 80) 32));
      v_6049 <- eval (add (leanSignExtend (extract v_5993 80 96) 32) (leanSignExtend (extract v_5996 80 96) 32));
      v_6059 <- eval (add (leanSignExtend (extract v_5993 96 112) 32) (leanSignExtend (extract v_5996 96 112) 32));
      v_6069 <- eval (add (leanSignExtend (extract v_5993 112 128) 32) (leanSignExtend (extract v_5996 112 128) 32));
      setRegister (lhs.of_reg v_3160) (concat (mux (sgt v_5999 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_5999 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_5999 16 32))) (concat (mux (sgt v_6009 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_6009 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_6009 16 32))) (concat (mux (sgt v_6019 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_6019 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_6019 16 32))) (concat (mux (sgt v_6029 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_6029 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_6029 16 32))) (concat (mux (sgt v_6039 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_6039 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_6039 16 32))) (concat (mux (sgt v_6049 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_6049 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_6049 16 32))) (concat (mux (sgt v_6059 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_6059 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_6059 16 32))) (mux (sgt v_6069 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_6069 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_6069 16 32))))))))));
      pure ()
    pat_end;
    pattern fun (v_3155 : Mem) (v_3156 : reg (bv 128)) => do
      v_10065 <- getRegister v_3156;
      v_10068 <- evaluateAddress v_3155;
      v_10069 <- load v_10068 16;
      v_10072 <- eval (add (leanSignExtend (extract v_10065 0 16) 32) (leanSignExtend (extract v_10069 0 16) 32));
      v_10082 <- eval (add (leanSignExtend (extract v_10065 16 32) 32) (leanSignExtend (extract v_10069 16 32) 32));
      v_10092 <- eval (add (leanSignExtend (extract v_10065 32 48) 32) (leanSignExtend (extract v_10069 32 48) 32));
      v_10102 <- eval (add (leanSignExtend (extract v_10065 48 64) 32) (leanSignExtend (extract v_10069 48 64) 32));
      v_10112 <- eval (add (leanSignExtend (extract v_10065 64 80) 32) (leanSignExtend (extract v_10069 64 80) 32));
      v_10122 <- eval (add (leanSignExtend (extract v_10065 80 96) 32) (leanSignExtend (extract v_10069 80 96) 32));
      v_10132 <- eval (add (leanSignExtend (extract v_10065 96 112) 32) (leanSignExtend (extract v_10069 96 112) 32));
      v_10142 <- eval (add (leanSignExtend (extract v_10065 112 128) 32) (leanSignExtend (extract v_10069 112 128) 32));
      setRegister (lhs.of_reg v_3156) (concat (mux (sgt v_10072 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_10072 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_10072 16 32))) (concat (mux (sgt v_10082 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_10082 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_10082 16 32))) (concat (mux (sgt v_10092 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_10092 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_10092 16 32))) (concat (mux (sgt v_10102 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_10102 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_10102 16 32))) (concat (mux (sgt v_10112 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_10112 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_10112 16 32))) (concat (mux (sgt v_10122 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_10122 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_10122 16 32))) (concat (mux (sgt v_10132 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_10132 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_10132 16 32))) (mux (sgt v_10142 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_10142 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_10142 16 32))))))))));
      pure ()
    pat_end
