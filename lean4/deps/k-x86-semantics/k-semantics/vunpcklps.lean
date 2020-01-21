def vunpcklps : instruction :=
  definst "vunpcklps" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- evaluateAddress mem_0;
      v_4 <- load v_3 16;
      v_5 <- getRegister (lhs.of_reg xmm_1);
      setRegister (lhs.of_reg xmm_2) (concat (concat (concat (extract v_4 64 96) (extract v_5 64 96)) (extract v_4 96 128)) (extract v_5 96 128));
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- evaluateAddress mem_0;
      v_4 <- load v_3 32;
      v_5 <- getRegister (lhs.of_reg ymm_1);
      setRegister (lhs.of_reg ymm_2) (concat (concat (concat (concat (extract v_4 64 96) (extract v_5 64 96)) (extract v_4 96 128)) (extract v_5 96 128)) (concat (concat (concat (extract v_4 192 224) (extract v_5 192 224)) (extract v_4 224 256)) (extract v_5 224 256)));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_0);
      v_4 <- getRegister (lhs.of_reg xmm_1);
      setRegister (lhs.of_reg xmm_2) (concat (concat (concat (extract v_3 64 96) (extract v_4 64 96)) (extract v_3 96 128)) (extract v_4 96 128));
      pure ()
    pat_end;
    pattern fun (ymm_0 : reg (bv 256)) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- getRegister (lhs.of_reg ymm_0);
      v_4 <- getRegister (lhs.of_reg ymm_1);
      setRegister (lhs.of_reg ymm_2) (concat (concat (concat (concat (extract v_3 64 96) (extract v_4 64 96)) (extract v_3 96 128)) (extract v_4 96 128)) (concat (concat (concat (extract v_3 192 224) (extract v_4 192 224)) (extract v_3 224 256)) (extract v_4 224 256)));
      pure ()
    pat_end
