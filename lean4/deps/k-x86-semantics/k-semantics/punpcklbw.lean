def punpcklbw1 : instruction :=
  definst "punpcklbw" $ do
    pattern fun (v_3261 : reg (bv 128)) (v_3262 : reg (bv 128)) => do
      v_8743 <- getRegister v_3261;
      v_8745 <- getRegister v_3262;
      setRegister (lhs.of_reg v_3262) (concat (concat (extract v_8743 64 72) (extract v_8745 64 72)) (concat (concat (extract v_8743 72 80) (extract v_8745 72 80)) (concat (concat (extract v_8743 80 88) (extract v_8745 80 88)) (concat (concat (extract v_8743 88 96) (extract v_8745 88 96)) (concat (concat (extract v_8743 96 104) (extract v_8745 96 104)) (concat (concat (extract v_8743 104 112) (extract v_8745 104 112)) (concat (concat (extract v_8743 112 120) (extract v_8745 112 120)) (concat (extract v_8743 120 128) (extract v_8745 120 128)))))))));
      pure ()
    pat_end;
    pattern fun (v_3258 : Mem) (v_3257 : reg (bv 128)) => do
      v_15185 <- evaluateAddress v_3258;
      v_15186 <- load v_15185 16;
      v_15188 <- getRegister v_3257;
      setRegister (lhs.of_reg v_3257) (concat (concat (extract v_15186 64 72) (extract v_15188 64 72)) (concat (concat (extract v_15186 72 80) (extract v_15188 72 80)) (concat (concat (extract v_15186 80 88) (extract v_15188 80 88)) (concat (concat (extract v_15186 88 96) (extract v_15188 88 96)) (concat (concat (extract v_15186 96 104) (extract v_15188 96 104)) (concat (concat (extract v_15186 104 112) (extract v_15188 104 112)) (concat (concat (extract v_15186 112 120) (extract v_15188 112 120)) (concat (extract v_15186 120 128) (extract v_15188 120 128)))))))));
      pure ()
    pat_end
