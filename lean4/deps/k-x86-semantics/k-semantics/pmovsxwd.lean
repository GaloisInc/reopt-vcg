def pmovsxwd1 : instruction :=
  definst "pmovsxwd" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 8;
      setRegister (lhs.of_reg xmm_1) (concat (sext (extract v_3 0 16) 32) (concat (sext (extract v_3 16 32) 32) (concat (sext (extract v_3 32 48) 32) (sext (extract v_3 48 64) 32))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister xmm_0;
      setRegister (lhs.of_reg xmm_1) (concat (sext (extract v_2 64 80) 32) (concat (sext (extract v_2 80 96) 32) (concat (sext (extract v_2 96 112) 32) (sext (extract v_2 112 128) 32))));
      pure ()
    pat_end
