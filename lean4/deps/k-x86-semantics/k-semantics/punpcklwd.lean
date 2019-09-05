def punpcklwd1 : instruction :=
  definst "punpcklwd" $ do
    pattern fun (v_3288 : reg (bv 128)) (v_3289 : reg (bv 128)) => do
      v_8805 <- getRegister v_3288;
      v_8807 <- getRegister v_3289;
      setRegister (lhs.of_reg v_3289) (concat (concat (extract v_8805 64 80) (extract v_8807 64 80)) (concat (concat (extract v_8805 80 96) (extract v_8807 80 96)) (concat (concat (extract v_8805 96 112) (extract v_8807 96 112)) (concat (extract v_8805 112 128) (extract v_8807 112 128)))));
      pure ()
    pat_end;
    pattern fun (v_3285 : Mem) (v_3284 : reg (bv 128)) => do
      v_15238 <- evaluateAddress v_3285;
      v_15239 <- load v_15238 16;
      v_15241 <- getRegister v_3284;
      setRegister (lhs.of_reg v_3284) (concat (concat (extract v_15239 64 80) (extract v_15241 64 80)) (concat (concat (extract v_15239 80 96) (extract v_15241 80 96)) (concat (concat (extract v_15239 96 112) (extract v_15241 96 112)) (concat (extract v_15239 112 128) (extract v_15241 112 128)))));
      pure ()
    pat_end
