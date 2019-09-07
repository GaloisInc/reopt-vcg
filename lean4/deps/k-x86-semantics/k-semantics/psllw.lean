def psllw1 : instruction :=
  definst "psllw" $ do
    pattern fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) => do
      v_2 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      v_3 <- getRegister xmm_1;
      v_4 <- eval (concat (expression.bv_nat 8 0) v_2);
      setRegister (lhs.of_reg xmm_1) (mux (ugt (concat (expression.bv_nat 56 0) v_2) (expression.bv_nat 64 15)) (expression.bv_nat 128 0) (concat (extract (shl (extract v_3 0 16) v_4) 0 16) (concat (extract (shl (extract v_3 16 32) v_4) 0 16) (concat (extract (shl (extract v_3 32 48) v_4) 0 16) (concat (extract (shl (extract v_3 48 64) v_4) 0 16) (concat (extract (shl (extract v_3 64 80) v_4) 0 16) (concat (extract (shl (extract v_3 80 96) v_4) 0 16) (concat (extract (shl (extract v_3 96 112) v_4) 0 16) (extract (shl (extract v_3 112 128) v_4) 0 16)))))))));
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 16;
      v_4 <- getRegister xmm_1;
      v_5 <- eval (extract v_3 112 128);
      setRegister (lhs.of_reg xmm_1) (mux (ugt (extract v_3 64 128) (expression.bv_nat 64 15)) (expression.bv_nat 128 0) (concat (extract (shl (extract v_4 0 16) v_5) 0 16) (concat (extract (shl (extract v_4 16 32) v_5) 0 16) (concat (extract (shl (extract v_4 32 48) v_5) 0 16) (concat (extract (shl (extract v_4 48 64) v_5) 0 16) (concat (extract (shl (extract v_4 64 80) v_5) 0 16) (concat (extract (shl (extract v_4 80 96) v_5) 0 16) (concat (extract (shl (extract v_4 96 112) v_5) 0 16) (extract (shl (extract v_4 112 128) v_5) 0 16)))))))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister xmm_0;
      v_3 <- getRegister xmm_1;
      v_4 <- eval (extract v_2 112 128);
      setRegister (lhs.of_reg xmm_1) (mux (ugt (extract v_2 64 128) (expression.bv_nat 64 15)) (expression.bv_nat 128 0) (concat (extract (shl (extract v_3 0 16) v_4) 0 16) (concat (extract (shl (extract v_3 16 32) v_4) 0 16) (concat (extract (shl (extract v_3 32 48) v_4) 0 16) (concat (extract (shl (extract v_3 48 64) v_4) 0 16) (concat (extract (shl (extract v_3 64 80) v_4) 0 16) (concat (extract (shl (extract v_3 80 96) v_4) 0 16) (concat (extract (shl (extract v_3 96 112) v_4) 0 16) (extract (shl (extract v_3 112 128) v_4) 0 16)))))))));
      pure ()
    pat_end
