def punpcklbw1 : instruction :=
  definst "punpcklbw" $ do
    pattern fun (v_3198 : reg (bv 128)) (v_3199 : reg (bv 128)) => do
      v_9129 <- getRegister v_3198;
      v_9131 <- getRegister v_3199;
      setRegister (lhs.of_reg v_3199) (concat (concat (extract v_9129 64 72) (extract v_9131 64 72)) (concat (concat (extract v_9129 72 80) (extract v_9131 72 80)) (concat (concat (extract v_9129 80 88) (extract v_9131 80 88)) (concat (concat (extract v_9129 88 96) (extract v_9131 88 96)) (concat (concat (extract v_9129 96 104) (extract v_9131 96 104)) (concat (concat (extract v_9129 104 112) (extract v_9131 104 112)) (concat (concat (extract v_9129 112 120) (extract v_9131 112 120)) (concat (extract v_9129 120 128) (extract v_9131 120 128)))))))));
      pure ()
    pat_end;
    pattern fun (v_3193 : Mem) (v_3194 : reg (bv 128)) => do
      v_16007 <- evaluateAddress v_3193;
      v_16008 <- load v_16007 16;
      v_16010 <- getRegister v_3194;
      setRegister (lhs.of_reg v_3194) (concat (concat (extract v_16008 64 72) (extract v_16010 64 72)) (concat (concat (extract v_16008 72 80) (extract v_16010 72 80)) (concat (concat (extract v_16008 80 88) (extract v_16010 80 88)) (concat (concat (extract v_16008 88 96) (extract v_16010 88 96)) (concat (concat (extract v_16008 96 104) (extract v_16010 96 104)) (concat (concat (extract v_16008 104 112) (extract v_16010 104 112)) (concat (concat (extract v_16008 112 120) (extract v_16010 112 120)) (concat (extract v_16008 120 128) (extract v_16010 120 128)))))))));
      pure ()
    pat_end
