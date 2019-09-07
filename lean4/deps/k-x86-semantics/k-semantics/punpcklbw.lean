def punpcklbw1 : instruction :=
  definst "punpcklbw" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 16;
      v_4 <- getRegister xmm_1;
      setRegister (lhs.of_reg xmm_1) (concat (concat (extract v_3 64 72) (extract v_4 64 72)) (concat (concat (extract v_3 72 80) (extract v_4 72 80)) (concat (concat (extract v_3 80 88) (extract v_4 80 88)) (concat (concat (extract v_3 88 96) (extract v_4 88 96)) (concat (concat (extract v_3 96 104) (extract v_4 96 104)) (concat (concat (extract v_3 104 112) (extract v_4 104 112)) (concat (concat (extract v_3 112 120) (extract v_4 112 120)) (concat (extract v_3 120 128) (extract v_4 120 128)))))))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister xmm_0;
      v_3 <- getRegister xmm_1;
      setRegister (lhs.of_reg xmm_1) (concat (concat (extract v_2 64 72) (extract v_3 64 72)) (concat (concat (extract v_2 72 80) (extract v_3 72 80)) (concat (concat (extract v_2 80 88) (extract v_3 80 88)) (concat (concat (extract v_2 88 96) (extract v_3 88 96)) (concat (concat (extract v_2 96 104) (extract v_3 96 104)) (concat (concat (extract v_2 104 112) (extract v_3 104 112)) (concat (concat (extract v_2 112 120) (extract v_3 112 120)) (concat (extract v_2 120 128) (extract v_3 120 128)))))))));
      pure ()
    pat_end
