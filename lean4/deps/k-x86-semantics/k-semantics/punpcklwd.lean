def punpcklwd1 : instruction :=
  definst "punpcklwd" $ do
    pattern fun (v_3316 : reg (bv 128)) (v_3317 : reg (bv 128)) => do
      v_8832 <- getRegister v_3316;
      v_8834 <- getRegister v_3317;
      setRegister (lhs.of_reg v_3317) (concat (concat (extract v_8832 64 80) (extract v_8834 64 80)) (concat (concat (extract v_8832 80 96) (extract v_8834 80 96)) (concat (concat (extract v_8832 96 112) (extract v_8834 96 112)) (concat (extract v_8832 112 128) (extract v_8834 112 128)))));
      pure ()
    pat_end;
    pattern fun (v_3312 : Mem) (v_3313 : reg (bv 128)) => do
      v_15214 <- evaluateAddress v_3312;
      v_15215 <- load v_15214 16;
      v_15217 <- getRegister v_3313;
      setRegister (lhs.of_reg v_3313) (concat (concat (extract v_15215 64 80) (extract v_15217 64 80)) (concat (concat (extract v_15215 80 96) (extract v_15217 80 96)) (concat (concat (extract v_15215 96 112) (extract v_15217 96 112)) (concat (extract v_15215 112 128) (extract v_15217 112 128)))));
      pure ()
    pat_end
