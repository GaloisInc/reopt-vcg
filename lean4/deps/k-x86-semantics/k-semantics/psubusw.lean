def psubusw1 : instruction :=
  definst "psubusw" $ do
    pattern fun (v_3226 : reg (bv 128)) (v_3227 : reg (bv 128)) => do
      v_8537 <- getRegister v_3227;
      v_8540 <- getRegister v_3226;
      v_8543 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_8537 0 16)) (concat (expression.bv_nat 2 0) (extract v_8540 0 16)));
      v_8553 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_8537 16 32)) (concat (expression.bv_nat 2 0) (extract v_8540 16 32)));
      v_8563 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_8537 32 48)) (concat (expression.bv_nat 2 0) (extract v_8540 32 48)));
      v_8573 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_8537 48 64)) (concat (expression.bv_nat 2 0) (extract v_8540 48 64)));
      v_8583 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_8537 64 80)) (concat (expression.bv_nat 2 0) (extract v_8540 64 80)));
      v_8593 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_8537 80 96)) (concat (expression.bv_nat 2 0) (extract v_8540 80 96)));
      v_8603 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_8537 96 112)) (concat (expression.bv_nat 2 0) (extract v_8540 96 112)));
      v_8613 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_8537 112 128)) (concat (expression.bv_nat 2 0) (extract v_8540 112 128)));
      setRegister (lhs.of_reg v_3227) (concat (mux (sgt v_8543 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_8543 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_8543 2 18))) (concat (mux (sgt v_8553 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_8553 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_8553 2 18))) (concat (mux (sgt v_8563 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_8563 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_8563 2 18))) (concat (mux (sgt v_8573 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_8573 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_8573 2 18))) (concat (mux (sgt v_8583 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_8583 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_8583 2 18))) (concat (mux (sgt v_8593 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_8593 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_8593 2 18))) (concat (mux (sgt v_8603 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_8603 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_8603 2 18))) (mux (sgt v_8613 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_8613 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_8613 2 18))))))))));
      pure ()
    pat_end;
    pattern fun (v_3222 : Mem) (v_3223 : reg (bv 128)) => do
      v_14949 <- getRegister v_3223;
      v_14952 <- evaluateAddress v_3222;
      v_14953 <- load v_14952 16;
      v_14956 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_14949 0 16)) (concat (expression.bv_nat 2 0) (extract v_14953 0 16)));
      v_14966 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_14949 16 32)) (concat (expression.bv_nat 2 0) (extract v_14953 16 32)));
      v_14976 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_14949 32 48)) (concat (expression.bv_nat 2 0) (extract v_14953 32 48)));
      v_14986 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_14949 48 64)) (concat (expression.bv_nat 2 0) (extract v_14953 48 64)));
      v_14996 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_14949 64 80)) (concat (expression.bv_nat 2 0) (extract v_14953 64 80)));
      v_15006 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_14949 80 96)) (concat (expression.bv_nat 2 0) (extract v_14953 80 96)));
      v_15016 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_14949 96 112)) (concat (expression.bv_nat 2 0) (extract v_14953 96 112)));
      v_15026 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_14949 112 128)) (concat (expression.bv_nat 2 0) (extract v_14953 112 128)));
      setRegister (lhs.of_reg v_3223) (concat (mux (sgt v_14956 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_14956 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_14956 2 18))) (concat (mux (sgt v_14966 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_14966 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_14966 2 18))) (concat (mux (sgt v_14976 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_14976 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_14976 2 18))) (concat (mux (sgt v_14986 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_14986 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_14986 2 18))) (concat (mux (sgt v_14996 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_14996 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_14996 2 18))) (concat (mux (sgt v_15006 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_15006 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_15006 2 18))) (concat (mux (sgt v_15016 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_15016 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_15016 2 18))) (mux (sgt v_15026 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_15026 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_15026 2 18))))))))));
      pure ()
    pat_end
