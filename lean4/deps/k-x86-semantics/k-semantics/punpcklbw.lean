def punpcklbw1 : instruction :=
  definst "punpcklbw" $ do
    pattern fun (v_3289 : reg (bv 128)) (v_3290 : reg (bv 128)) => do
      v_8770 <- getRegister v_3289;
      v_8772 <- getRegister v_3290;
      setRegister (lhs.of_reg v_3290) (concat (concat (extract v_8770 64 72) (extract v_8772 64 72)) (concat (concat (extract v_8770 72 80) (extract v_8772 72 80)) (concat (concat (extract v_8770 80 88) (extract v_8772 80 88)) (concat (concat (extract v_8770 88 96) (extract v_8772 88 96)) (concat (concat (extract v_8770 96 104) (extract v_8772 96 104)) (concat (concat (extract v_8770 104 112) (extract v_8772 104 112)) (concat (concat (extract v_8770 112 120) (extract v_8772 112 120)) (concat (extract v_8770 120 128) (extract v_8772 120 128)))))))));
      pure ()
    pat_end;
    pattern fun (v_3285 : Mem) (v_3286 : reg (bv 128)) => do
      v_15161 <- evaluateAddress v_3285;
      v_15162 <- load v_15161 16;
      v_15164 <- getRegister v_3286;
      setRegister (lhs.of_reg v_3286) (concat (concat (extract v_15162 64 72) (extract v_15164 64 72)) (concat (concat (extract v_15162 72 80) (extract v_15164 72 80)) (concat (concat (extract v_15162 80 88) (extract v_15164 80 88)) (concat (concat (extract v_15162 88 96) (extract v_15164 88 96)) (concat (concat (extract v_15162 96 104) (extract v_15164 96 104)) (concat (concat (extract v_15162 104 112) (extract v_15164 104 112)) (concat (concat (extract v_15162 112 120) (extract v_15164 112 120)) (concat (extract v_15162 120 128) (extract v_15164 120 128)))))))));
      pure ()
    pat_end
