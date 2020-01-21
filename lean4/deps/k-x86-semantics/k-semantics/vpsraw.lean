def vpsraw : instruction :=
  definst "vpsraw" $ do
    pattern fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_1);
      v_4 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      v_5 <- eval (mux (ugt (concat (expression.bv_nat 56 0) v_4) (expression.bv_nat 64 15)) (expression.bv_nat 16 16) (concat (expression.bv_nat 8 0) v_4));
      setRegister (lhs.of_reg xmm_2) (concat (ashr (extract v_3 0 16) v_5) (concat (ashr (extract v_3 16 32) v_5) (concat (ashr (extract v_3 32 48) v_5) (concat (ashr (extract v_3 48 64) v_5) (concat (ashr (extract v_3 64 80) v_5) (concat (ashr (extract v_3 80 96) v_5) (concat (ashr (extract v_3 96 112) v_5) (ashr (extract v_3 112 128) v_5))))))));
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- getRegister (lhs.of_reg ymm_1);
      v_4 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      v_5 <- eval (mux (ugt (concat (expression.bv_nat 56 0) v_4) (expression.bv_nat 64 15)) (expression.bv_nat 16 16) (concat (expression.bv_nat 8 0) v_4));
      setRegister (lhs.of_reg ymm_2) (concat (ashr (extract v_3 0 16) v_5) (concat (ashr (extract v_3 16 32) v_5) (concat (ashr (extract v_3 32 48) v_5) (concat (ashr (extract v_3 48 64) v_5) (concat (ashr (extract v_3 64 80) v_5) (concat (ashr (extract v_3 80 96) v_5) (concat (ashr (extract v_3 96 112) v_5) (concat (ashr (extract v_3 112 128) v_5) (concat (ashr (extract v_3 128 144) v_5) (concat (ashr (extract v_3 144 160) v_5) (concat (ashr (extract v_3 160 176) v_5) (concat (ashr (extract v_3 176 192) v_5) (concat (ashr (extract v_3 192 208) v_5) (concat (ashr (extract v_3 208 224) v_5) (concat (ashr (extract v_3 224 240) v_5) (ashr (extract v_3 240 256) v_5))))))))))))))));
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_1);
      v_4 <- evaluateAddress mem_0;
      v_5 <- load v_4 16;
      v_6 <- eval (mux (ugt (extract v_5 64 128) (expression.bv_nat 64 15)) (expression.bv_nat 16 16) (extract v_5 112 128));
      setRegister (lhs.of_reg xmm_2) (concat (ashr (extract v_3 0 16) v_6) (concat (ashr (extract v_3 16 32) v_6) (concat (ashr (extract v_3 32 48) v_6) (concat (ashr (extract v_3 48 64) v_6) (concat (ashr (extract v_3 64 80) v_6) (concat (ashr (extract v_3 80 96) v_6) (concat (ashr (extract v_3 96 112) v_6) (ashr (extract v_3 112 128) v_6))))))));
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- getRegister (lhs.of_reg ymm_1);
      v_4 <- evaluateAddress mem_0;
      v_5 <- load v_4 16;
      v_6 <- eval (mux (ugt (extract v_5 64 128) (expression.bv_nat 64 15)) (expression.bv_nat 16 16) (extract v_5 112 128));
      setRegister (lhs.of_reg ymm_2) (concat (ashr (extract v_3 0 16) v_6) (concat (ashr (extract v_3 16 32) v_6) (concat (ashr (extract v_3 32 48) v_6) (concat (ashr (extract v_3 48 64) v_6) (concat (ashr (extract v_3 64 80) v_6) (concat (ashr (extract v_3 80 96) v_6) (concat (ashr (extract v_3 96 112) v_6) (concat (ashr (extract v_3 112 128) v_6) (concat (ashr (extract v_3 128 144) v_6) (concat (ashr (extract v_3 144 160) v_6) (concat (ashr (extract v_3 160 176) v_6) (concat (ashr (extract v_3 176 192) v_6) (concat (ashr (extract v_3 192 208) v_6) (concat (ashr (extract v_3 208 224) v_6) (concat (ashr (extract v_3 224 240) v_6) (ashr (extract v_3 240 256) v_6))))))))))))))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_1);
      v_4 <- getRegister (lhs.of_reg xmm_0);
      v_5 <- eval (mux (ugt (extract v_4 64 128) (expression.bv_nat 64 15)) (expression.bv_nat 16 16) (extract v_4 112 128));
      setRegister (lhs.of_reg xmm_2) (concat (ashr (extract v_3 0 16) v_5) (concat (ashr (extract v_3 16 32) v_5) (concat (ashr (extract v_3 32 48) v_5) (concat (ashr (extract v_3 48 64) v_5) (concat (ashr (extract v_3 64 80) v_5) (concat (ashr (extract v_3 80 96) v_5) (concat (ashr (extract v_3 96 112) v_5) (ashr (extract v_3 112 128) v_5))))))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- getRegister (lhs.of_reg ymm_1);
      v_4 <- getRegister (lhs.of_reg xmm_0);
      v_5 <- eval (mux (ugt (extract v_4 64 128) (expression.bv_nat 64 15)) (expression.bv_nat 16 16) (extract v_4 112 128));
      setRegister (lhs.of_reg ymm_2) (concat (ashr (extract v_3 0 16) v_5) (concat (ashr (extract v_3 16 32) v_5) (concat (ashr (extract v_3 32 48) v_5) (concat (ashr (extract v_3 48 64) v_5) (concat (ashr (extract v_3 64 80) v_5) (concat (ashr (extract v_3 80 96) v_5) (concat (ashr (extract v_3 96 112) v_5) (concat (ashr (extract v_3 112 128) v_5) (concat (ashr (extract v_3 128 144) v_5) (concat (ashr (extract v_3 144 160) v_5) (concat (ashr (extract v_3 160 176) v_5) (concat (ashr (extract v_3 176 192) v_5) (concat (ashr (extract v_3 192 208) v_5) (concat (ashr (extract v_3 208 224) v_5) (concat (ashr (extract v_3 224 240) v_5) (ashr (extract v_3 240 256) v_5))))))))))))))));
      pure ()
    pat_end
