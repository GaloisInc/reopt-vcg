def vpmaxud1 : instruction :=
  definst "vpmaxud" $ do
    pattern fun (v_2407 : reg (bv 128)) (v_2408 : reg (bv 128)) (v_2409 : reg (bv 128)) => do
      v_4161 <- getRegister v_2408;
      v_4162 <- eval (extract v_4161 0 32);
      v_4163 <- getRegister v_2407;
      v_4164 <- eval (extract v_4163 0 32);
      v_4167 <- eval (extract v_4161 32 64);
      v_4168 <- eval (extract v_4163 32 64);
      v_4171 <- eval (extract v_4161 64 96);
      v_4172 <- eval (extract v_4163 64 96);
      v_4175 <- eval (extract v_4161 96 128);
      v_4176 <- eval (extract v_4163 96 128);
      setRegister (lhs.of_reg v_2409) (concat (mux (ugt v_4162 v_4164) v_4162 v_4164) (concat (mux (ugt v_4167 v_4168) v_4167 v_4168) (concat (mux (ugt v_4171 v_4172) v_4171 v_4172) (mux (ugt v_4175 v_4176) v_4175 v_4176))));
      pure ()
    pat_end;
    pattern fun (v_2418 : reg (bv 256)) (v_2419 : reg (bv 256)) (v_2420 : reg (bv 256)) => do
      v_4188 <- getRegister v_2419;
      v_4189 <- eval (extract v_4188 0 32);
      v_4190 <- getRegister v_2418;
      v_4191 <- eval (extract v_4190 0 32);
      v_4194 <- eval (extract v_4188 32 64);
      v_4195 <- eval (extract v_4190 32 64);
      v_4198 <- eval (extract v_4188 64 96);
      v_4199 <- eval (extract v_4190 64 96);
      v_4202 <- eval (extract v_4188 96 128);
      v_4203 <- eval (extract v_4190 96 128);
      v_4206 <- eval (extract v_4188 128 160);
      v_4207 <- eval (extract v_4190 128 160);
      v_4210 <- eval (extract v_4188 160 192);
      v_4211 <- eval (extract v_4190 160 192);
      v_4214 <- eval (extract v_4188 192 224);
      v_4215 <- eval (extract v_4190 192 224);
      v_4218 <- eval (extract v_4188 224 256);
      v_4219 <- eval (extract v_4190 224 256);
      setRegister (lhs.of_reg v_2420) (concat (mux (ugt v_4189 v_4191) v_4189 v_4191) (concat (mux (ugt v_4194 v_4195) v_4194 v_4195) (concat (mux (ugt v_4198 v_4199) v_4198 v_4199) (concat (mux (ugt v_4202 v_4203) v_4202 v_4203) (concat (mux (ugt v_4206 v_4207) v_4206 v_4207) (concat (mux (ugt v_4210 v_4211) v_4210 v_4211) (concat (mux (ugt v_4214 v_4215) v_4214 v_4215) (mux (ugt v_4218 v_4219) v_4218 v_4219))))))));
      pure ()
    pat_end;
    pattern fun (v_2404 : Mem) (v_2402 : reg (bv 128)) (v_2403 : reg (bv 128)) => do
      v_11597 <- getRegister v_2402;
      v_11598 <- eval (extract v_11597 0 32);
      v_11599 <- evaluateAddress v_2404;
      v_11600 <- load v_11599 16;
      v_11601 <- eval (extract v_11600 0 32);
      v_11604 <- eval (extract v_11597 32 64);
      v_11605 <- eval (extract v_11600 32 64);
      v_11608 <- eval (extract v_11597 64 96);
      v_11609 <- eval (extract v_11600 64 96);
      v_11612 <- eval (extract v_11597 96 128);
      v_11613 <- eval (extract v_11600 96 128);
      setRegister (lhs.of_reg v_2403) (concat (mux (ugt v_11598 v_11601) v_11598 v_11601) (concat (mux (ugt v_11604 v_11605) v_11604 v_11605) (concat (mux (ugt v_11608 v_11609) v_11608 v_11609) (mux (ugt v_11612 v_11613) v_11612 v_11613))));
      pure ()
    pat_end;
    pattern fun (v_2413 : Mem) (v_2414 : reg (bv 256)) (v_2415 : reg (bv 256)) => do
      v_11620 <- getRegister v_2414;
      v_11621 <- eval (extract v_11620 0 32);
      v_11622 <- evaluateAddress v_2413;
      v_11623 <- load v_11622 32;
      v_11624 <- eval (extract v_11623 0 32);
      v_11627 <- eval (extract v_11620 32 64);
      v_11628 <- eval (extract v_11623 32 64);
      v_11631 <- eval (extract v_11620 64 96);
      v_11632 <- eval (extract v_11623 64 96);
      v_11635 <- eval (extract v_11620 96 128);
      v_11636 <- eval (extract v_11623 96 128);
      v_11639 <- eval (extract v_11620 128 160);
      v_11640 <- eval (extract v_11623 128 160);
      v_11643 <- eval (extract v_11620 160 192);
      v_11644 <- eval (extract v_11623 160 192);
      v_11647 <- eval (extract v_11620 192 224);
      v_11648 <- eval (extract v_11623 192 224);
      v_11651 <- eval (extract v_11620 224 256);
      v_11652 <- eval (extract v_11623 224 256);
      setRegister (lhs.of_reg v_2415) (concat (mux (ugt v_11621 v_11624) v_11621 v_11624) (concat (mux (ugt v_11627 v_11628) v_11627 v_11628) (concat (mux (ugt v_11631 v_11632) v_11631 v_11632) (concat (mux (ugt v_11635 v_11636) v_11635 v_11636) (concat (mux (ugt v_11639 v_11640) v_11639 v_11640) (concat (mux (ugt v_11643 v_11644) v_11643 v_11644) (concat (mux (ugt v_11647 v_11648) v_11647 v_11648) (mux (ugt v_11651 v_11652) v_11651 v_11652))))))));
      pure ()
    pat_end
