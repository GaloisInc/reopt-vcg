def vpmovsxbq : instruction :=
  definst "vpmovsxbq" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 2;
      setRegister (lhs.of_reg xmm_1) (concat (sext (extract v_3 0 8) 64) (sext (extract v_3 8 16) 64));
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 4;
      setRegister (lhs.of_reg ymm_1) (concat (sext (extract v_3 0 8) 64) (concat (sext (extract v_3 8 16) 64) (concat (sext (extract v_3 16 24) 64) (sext (extract v_3 24 32) 64))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_0);
      setRegister (lhs.of_reg xmm_1) (concat (sext (extract v_2 112 120) 64) (sext (extract v_2 120 128) 64));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (ymm_1 : reg (bv 256)) => do
      v_2 <- getRegister (lhs.of_reg xmm_0);
      setRegister (lhs.of_reg ymm_1) (concat (sext (extract v_2 96 104) 64) (concat (sext (extract v_2 104 112) 64) (concat (sext (extract v_2 112 120) 64) (sext (extract v_2 120 128) 64))));
      pure ()
    pat_end
