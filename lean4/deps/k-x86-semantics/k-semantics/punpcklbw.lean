def punpcklbw1 : instruction :=
  definst "punpcklbw" $ do
    pattern fun (v_3212 : reg (bv 128)) (v_3213 : reg (bv 128)) => do
      v_8809 <- getRegister v_3212;
      v_8811 <- getRegister v_3213;
      setRegister (lhs.of_reg v_3213) (concat (concat (extract v_8809 64 72) (extract v_8811 64 72)) (concat (concat (extract v_8809 72 80) (extract v_8811 72 80)) (concat (concat (extract v_8809 80 88) (extract v_8811 80 88)) (concat (concat (extract v_8809 88 96) (extract v_8811 88 96)) (concat (concat (extract v_8809 96 104) (extract v_8811 96 104)) (concat (concat (extract v_8809 104 112) (extract v_8811 104 112)) (concat (concat (extract v_8809 112 120) (extract v_8811 112 120)) (concat (extract v_8809 120 128) (extract v_8811 120 128)))))))));
      pure ()
    pat_end;
    pattern fun (v_3208 : Mem) (v_3209 : reg (bv 128)) => do
      v_15388 <- evaluateAddress v_3208;
      v_15389 <- load v_15388 16;
      v_15391 <- getRegister v_3209;
      setRegister (lhs.of_reg v_3209) (concat (concat (extract v_15389 64 72) (extract v_15391 64 72)) (concat (concat (extract v_15389 72 80) (extract v_15391 72 80)) (concat (concat (extract v_15389 80 88) (extract v_15391 80 88)) (concat (concat (extract v_15389 88 96) (extract v_15391 88 96)) (concat (concat (extract v_15389 96 104) (extract v_15391 96 104)) (concat (concat (extract v_15389 104 112) (extract v_15391 104 112)) (concat (concat (extract v_15389 112 120) (extract v_15391 112 120)) (concat (extract v_15389 120 128) (extract v_15391 120 128)))))))));
      pure ()
    pat_end
