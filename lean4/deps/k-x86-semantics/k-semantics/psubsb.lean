def psubsb1 : instruction :=
  definst "psubsb" $ do
    pattern fun (v_3171 : reg (bv 128)) (v_3172 : reg (bv 128)) => do
      v_8052 <- getRegister v_3172;
      v_8055 <- getRegister v_3171;
      v_8058 <- eval (sub (sext (extract v_8052 0 8) 10) (sext (extract v_8055 0 8) 10));
      v_8068 <- eval (sub (sext (extract v_8052 8 16) 10) (sext (extract v_8055 8 16) 10));
      v_8078 <- eval (sub (sext (extract v_8052 16 24) 10) (sext (extract v_8055 16 24) 10));
      v_8088 <- eval (sub (sext (extract v_8052 24 32) 10) (sext (extract v_8055 24 32) 10));
      v_8098 <- eval (sub (sext (extract v_8052 32 40) 10) (sext (extract v_8055 32 40) 10));
      v_8108 <- eval (sub (sext (extract v_8052 40 48) 10) (sext (extract v_8055 40 48) 10));
      v_8118 <- eval (sub (sext (extract v_8052 48 56) 10) (sext (extract v_8055 48 56) 10));
      v_8128 <- eval (sub (sext (extract v_8052 56 64) 10) (sext (extract v_8055 56 64) 10));
      v_8138 <- eval (sub (sext (extract v_8052 64 72) 10) (sext (extract v_8055 64 72) 10));
      v_8148 <- eval (sub (sext (extract v_8052 72 80) 10) (sext (extract v_8055 72 80) 10));
      v_8158 <- eval (sub (sext (extract v_8052 80 88) 10) (sext (extract v_8055 80 88) 10));
      v_8168 <- eval (sub (sext (extract v_8052 88 96) 10) (sext (extract v_8055 88 96) 10));
      v_8178 <- eval (sub (sext (extract v_8052 96 104) 10) (sext (extract v_8055 96 104) 10));
      v_8188 <- eval (sub (sext (extract v_8052 104 112) 10) (sext (extract v_8055 104 112) 10));
      v_8198 <- eval (sub (sext (extract v_8052 112 120) 10) (sext (extract v_8055 112 120) 10));
      v_8208 <- eval (sub (sext (extract v_8052 120 128) 10) (sext (extract v_8055 120 128) 10));
      setRegister (lhs.of_reg v_3172) (concat (mux (sgt v_8058 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_8058 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_8058 2 10))) (concat (mux (sgt v_8068 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_8068 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_8068 2 10))) (concat (mux (sgt v_8078 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_8078 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_8078 2 10))) (concat (mux (sgt v_8088 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_8088 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_8088 2 10))) (concat (mux (sgt v_8098 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_8098 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_8098 2 10))) (concat (mux (sgt v_8108 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_8108 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_8108 2 10))) (concat (mux (sgt v_8118 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_8118 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_8118 2 10))) (concat (mux (sgt v_8128 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_8128 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_8128 2 10))) (concat (mux (sgt v_8138 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_8138 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_8138 2 10))) (concat (mux (sgt v_8148 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_8148 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_8148 2 10))) (concat (mux (sgt v_8158 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_8158 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_8158 2 10))) (concat (mux (sgt v_8168 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_8168 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_8168 2 10))) (concat (mux (sgt v_8178 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_8178 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_8178 2 10))) (concat (mux (sgt v_8188 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_8188 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_8188 2 10))) (concat (mux (sgt v_8198 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_8198 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_8198 2 10))) (mux (sgt v_8208 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_8208 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_8208 2 10))))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_3168 : Mem) (v_3167 : reg (bv 128)) => do
      v_14524 <- getRegister v_3167;
      v_14527 <- evaluateAddress v_3168;
      v_14528 <- load v_14527 16;
      v_14531 <- eval (sub (sext (extract v_14524 0 8) 10) (sext (extract v_14528 0 8) 10));
      v_14541 <- eval (sub (sext (extract v_14524 8 16) 10) (sext (extract v_14528 8 16) 10));
      v_14551 <- eval (sub (sext (extract v_14524 16 24) 10) (sext (extract v_14528 16 24) 10));
      v_14561 <- eval (sub (sext (extract v_14524 24 32) 10) (sext (extract v_14528 24 32) 10));
      v_14571 <- eval (sub (sext (extract v_14524 32 40) 10) (sext (extract v_14528 32 40) 10));
      v_14581 <- eval (sub (sext (extract v_14524 40 48) 10) (sext (extract v_14528 40 48) 10));
      v_14591 <- eval (sub (sext (extract v_14524 48 56) 10) (sext (extract v_14528 48 56) 10));
      v_14601 <- eval (sub (sext (extract v_14524 56 64) 10) (sext (extract v_14528 56 64) 10));
      v_14611 <- eval (sub (sext (extract v_14524 64 72) 10) (sext (extract v_14528 64 72) 10));
      v_14621 <- eval (sub (sext (extract v_14524 72 80) 10) (sext (extract v_14528 72 80) 10));
      v_14631 <- eval (sub (sext (extract v_14524 80 88) 10) (sext (extract v_14528 80 88) 10));
      v_14641 <- eval (sub (sext (extract v_14524 88 96) 10) (sext (extract v_14528 88 96) 10));
      v_14651 <- eval (sub (sext (extract v_14524 96 104) 10) (sext (extract v_14528 96 104) 10));
      v_14661 <- eval (sub (sext (extract v_14524 104 112) 10) (sext (extract v_14528 104 112) 10));
      v_14671 <- eval (sub (sext (extract v_14524 112 120) 10) (sext (extract v_14528 112 120) 10));
      v_14681 <- eval (sub (sext (extract v_14524 120 128) 10) (sext (extract v_14528 120 128) 10));
      setRegister (lhs.of_reg v_3167) (concat (mux (sgt v_14531 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_14531 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_14531 2 10))) (concat (mux (sgt v_14541 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_14541 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_14541 2 10))) (concat (mux (sgt v_14551 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_14551 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_14551 2 10))) (concat (mux (sgt v_14561 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_14561 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_14561 2 10))) (concat (mux (sgt v_14571 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_14571 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_14571 2 10))) (concat (mux (sgt v_14581 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_14581 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_14581 2 10))) (concat (mux (sgt v_14591 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_14591 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_14591 2 10))) (concat (mux (sgt v_14601 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_14601 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_14601 2 10))) (concat (mux (sgt v_14611 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_14611 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_14611 2 10))) (concat (mux (sgt v_14621 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_14621 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_14621 2 10))) (concat (mux (sgt v_14631 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_14631 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_14631 2 10))) (concat (mux (sgt v_14641 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_14641 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_14641 2 10))) (concat (mux (sgt v_14651 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_14651 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_14651 2 10))) (concat (mux (sgt v_14661 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_14661 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_14661 2 10))) (concat (mux (sgt v_14671 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_14671 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_14671 2 10))) (mux (sgt v_14681 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_14681 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_14681 2 10))))))))))))))))));
      pure ()
    pat_end
