def psubw1 : instruction :=
  definst "psubw" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister xmm_1;
      v_3 <- evaluateAddress mem_0;
      v_4 <- load v_3 16;
      setRegister (lhs.of_reg xmm_1) (concat (sub (extract v_2 0 16) (extract v_4 0 16)) (concat (sub (extract v_2 16 32) (extract v_4 16 32)) (concat (sub (extract v_2 32 48) (extract v_4 32 48)) (concat (sub (extract v_2 48 64) (extract v_4 48 64)) (concat (sub (extract v_2 64 80) (extract v_4 64 80)) (concat (sub (extract v_2 80 96) (extract v_4 80 96)) (concat (sub (extract v_2 96 112) (extract v_4 96 112)) (sub (extract v_2 112 128) (extract v_4 112 128)))))))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister xmm_1;
      v_3 <- getRegister xmm_0;
      setRegister (lhs.of_reg xmm_1) (concat (sub (extract v_2 0 16) (extract v_3 0 16)) (concat (sub (extract v_2 16 32) (extract v_3 16 32)) (concat (sub (extract v_2 32 48) (extract v_3 32 48)) (concat (sub (extract v_2 48 64) (extract v_3 48 64)) (concat (sub (extract v_2 64 80) (extract v_3 64 80)) (concat (sub (extract v_2 80 96) (extract v_3 80 96)) (concat (sub (extract v_2 96 112) (extract v_3 96 112)) (sub (extract v_2 112 128) (extract v_3 112 128)))))))));
      pure ()
    pat_end
