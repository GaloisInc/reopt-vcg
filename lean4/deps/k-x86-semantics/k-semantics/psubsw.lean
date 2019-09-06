def psubsw1 : instruction :=
  definst "psubsw" $ do
    pattern fun (v_3208 : reg (bv 128)) (v_3209 : reg (bv 128)) => do
      v_8261 <- getRegister v_3209;
      v_8264 <- getRegister v_3208;
      v_8267 <- eval (sub (sext (extract v_8261 0 16) 18) (sext (extract v_8264 0 16) 18));
      v_8277 <- eval (sub (sext (extract v_8261 16 32) 18) (sext (extract v_8264 16 32) 18));
      v_8287 <- eval (sub (sext (extract v_8261 32 48) 18) (sext (extract v_8264 32 48) 18));
      v_8297 <- eval (sub (sext (extract v_8261 48 64) 18) (sext (extract v_8264 48 64) 18));
      v_8307 <- eval (sub (sext (extract v_8261 64 80) 18) (sext (extract v_8264 64 80) 18));
      v_8317 <- eval (sub (sext (extract v_8261 80 96) 18) (sext (extract v_8264 80 96) 18));
      v_8327 <- eval (sub (sext (extract v_8261 96 112) 18) (sext (extract v_8264 96 112) 18));
      v_8337 <- eval (sub (sext (extract v_8261 112 128) 18) (sext (extract v_8264 112 128) 18));
      setRegister (lhs.of_reg v_3209) (concat (mux (sgt v_8267 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_8267 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_8267 2 18))) (concat (mux (sgt v_8277 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_8277 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_8277 2 18))) (concat (mux (sgt v_8287 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_8287 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_8287 2 18))) (concat (mux (sgt v_8297 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_8297 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_8297 2 18))) (concat (mux (sgt v_8307 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_8307 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_8307 2 18))) (concat (mux (sgt v_8317 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_8317 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_8317 2 18))) (concat (mux (sgt v_8327 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_8327 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_8327 2 18))) (mux (sgt v_8337 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_8337 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_8337 2 18))))))))));
      pure ()
    pat_end;
    pattern fun (v_3204 : Mem) (v_3205 : reg (bv 128)) => do
      v_14679 <- getRegister v_3205;
      v_14682 <- evaluateAddress v_3204;
      v_14683 <- load v_14682 16;
      v_14686 <- eval (sub (sext (extract v_14679 0 16) 18) (sext (extract v_14683 0 16) 18));
      v_14696 <- eval (sub (sext (extract v_14679 16 32) 18) (sext (extract v_14683 16 32) 18));
      v_14706 <- eval (sub (sext (extract v_14679 32 48) 18) (sext (extract v_14683 32 48) 18));
      v_14716 <- eval (sub (sext (extract v_14679 48 64) 18) (sext (extract v_14683 48 64) 18));
      v_14726 <- eval (sub (sext (extract v_14679 64 80) 18) (sext (extract v_14683 64 80) 18));
      v_14736 <- eval (sub (sext (extract v_14679 80 96) 18) (sext (extract v_14683 80 96) 18));
      v_14746 <- eval (sub (sext (extract v_14679 96 112) 18) (sext (extract v_14683 96 112) 18));
      v_14756 <- eval (sub (sext (extract v_14679 112 128) 18) (sext (extract v_14683 112 128) 18));
      setRegister (lhs.of_reg v_3205) (concat (mux (sgt v_14686 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_14686 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_14686 2 18))) (concat (mux (sgt v_14696 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_14696 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_14696 2 18))) (concat (mux (sgt v_14706 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_14706 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_14706 2 18))) (concat (mux (sgt v_14716 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_14716 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_14716 2 18))) (concat (mux (sgt v_14726 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_14726 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_14726 2 18))) (concat (mux (sgt v_14736 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_14736 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_14736 2 18))) (concat (mux (sgt v_14746 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_14746 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_14746 2 18))) (mux (sgt v_14756 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_14756 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_14756 2 18))))))))));
      pure ()
    pat_end
