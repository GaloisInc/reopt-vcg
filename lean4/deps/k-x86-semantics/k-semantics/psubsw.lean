def psubsw1 : instruction :=
  definst "psubsw" $ do
    pattern fun (v_3131 : reg (bv 128)) (v_3132 : reg (bv 128)) => do
      v_8299 <- getRegister v_3132;
      v_8302 <- getRegister v_3131;
      v_8305 <- eval (sub (leanSignExtend (extract v_8299 0 16) 18) (leanSignExtend (extract v_8302 0 16) 18));
      v_8315 <- eval (sub (leanSignExtend (extract v_8299 16 32) 18) (leanSignExtend (extract v_8302 16 32) 18));
      v_8325 <- eval (sub (leanSignExtend (extract v_8299 32 48) 18) (leanSignExtend (extract v_8302 32 48) 18));
      v_8335 <- eval (sub (leanSignExtend (extract v_8299 48 64) 18) (leanSignExtend (extract v_8302 48 64) 18));
      v_8345 <- eval (sub (leanSignExtend (extract v_8299 64 80) 18) (leanSignExtend (extract v_8302 64 80) 18));
      v_8355 <- eval (sub (leanSignExtend (extract v_8299 80 96) 18) (leanSignExtend (extract v_8302 80 96) 18));
      v_8365 <- eval (sub (leanSignExtend (extract v_8299 96 112) 18) (leanSignExtend (extract v_8302 96 112) 18));
      v_8375 <- eval (sub (leanSignExtend (extract v_8299 112 128) 18) (leanSignExtend (extract v_8302 112 128) 18));
      setRegister (lhs.of_reg v_3132) (concat (mux (sgt v_8305 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_8305 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_8305 2 18))) (concat (mux (sgt v_8315 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_8315 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_8315 2 18))) (concat (mux (sgt v_8325 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_8325 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_8325 2 18))) (concat (mux (sgt v_8335 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_8335 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_8335 2 18))) (concat (mux (sgt v_8345 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_8345 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_8345 2 18))) (concat (mux (sgt v_8355 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_8355 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_8355 2 18))) (concat (mux (sgt v_8365 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_8365 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_8365 2 18))) (mux (sgt v_8375 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_8375 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_8375 2 18))))))))));
      pure ()
    pat_end;
    pattern fun (v_3127 : Mem) (v_3128 : reg (bv 128)) => do
      v_14905 <- getRegister v_3128;
      v_14908 <- evaluateAddress v_3127;
      v_14909 <- load v_14908 16;
      v_14912 <- eval (sub (leanSignExtend (extract v_14905 0 16) 18) (leanSignExtend (extract v_14909 0 16) 18));
      v_14922 <- eval (sub (leanSignExtend (extract v_14905 16 32) 18) (leanSignExtend (extract v_14909 16 32) 18));
      v_14932 <- eval (sub (leanSignExtend (extract v_14905 32 48) 18) (leanSignExtend (extract v_14909 32 48) 18));
      v_14942 <- eval (sub (leanSignExtend (extract v_14905 48 64) 18) (leanSignExtend (extract v_14909 48 64) 18));
      v_14952 <- eval (sub (leanSignExtend (extract v_14905 64 80) 18) (leanSignExtend (extract v_14909 64 80) 18));
      v_14962 <- eval (sub (leanSignExtend (extract v_14905 80 96) 18) (leanSignExtend (extract v_14909 80 96) 18));
      v_14972 <- eval (sub (leanSignExtend (extract v_14905 96 112) 18) (leanSignExtend (extract v_14909 96 112) 18));
      v_14982 <- eval (sub (leanSignExtend (extract v_14905 112 128) 18) (leanSignExtend (extract v_14909 112 128) 18));
      setRegister (lhs.of_reg v_3128) (concat (mux (sgt v_14912 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_14912 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_14912 2 18))) (concat (mux (sgt v_14922 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_14922 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_14922 2 18))) (concat (mux (sgt v_14932 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_14932 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_14932 2 18))) (concat (mux (sgt v_14942 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_14942 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_14942 2 18))) (concat (mux (sgt v_14952 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_14952 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_14952 2 18))) (concat (mux (sgt v_14962 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_14962 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_14962 2 18))) (concat (mux (sgt v_14972 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_14972 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_14972 2 18))) (mux (sgt v_14982 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_14982 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_14982 2 18))))))))));
      pure ()
    pat_end
