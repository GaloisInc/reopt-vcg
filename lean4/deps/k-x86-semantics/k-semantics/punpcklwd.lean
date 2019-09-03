def punpcklwd1 : instruction :=
  definst "punpcklwd" $ do
    pattern fun (v_3239 : reg (bv 128)) (v_3240 : reg (bv 128)) => do
      v_8871 <- getRegister v_3239;
      v_8873 <- getRegister v_3240;
      setRegister (lhs.of_reg v_3240) (concat (concat (extract v_8871 64 80) (extract v_8873 64 80)) (concat (concat (extract v_8871 80 96) (extract v_8873 80 96)) (concat (concat (extract v_8871 96 112) (extract v_8873 96 112)) (concat (extract v_8871 112 128) (extract v_8873 112 128)))));
      pure ()
    pat_end;
    pattern fun (v_3235 : Mem) (v_3236 : reg (bv 128)) => do
      v_15441 <- evaluateAddress v_3235;
      v_15442 <- load v_15441 16;
      v_15444 <- getRegister v_3236;
      setRegister (lhs.of_reg v_3236) (concat (concat (extract v_15442 64 80) (extract v_15444 64 80)) (concat (concat (extract v_15442 80 96) (extract v_15444 80 96)) (concat (concat (extract v_15442 96 112) (extract v_15444 96 112)) (concat (extract v_15442 112 128) (extract v_15444 112 128)))));
      pure ()
    pat_end
