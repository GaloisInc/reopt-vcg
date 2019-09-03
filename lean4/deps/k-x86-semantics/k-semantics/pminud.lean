def pminud1 : instruction :=
  definst "pminud" $ do
    pattern fun (v_2652 : reg (bv 128)) (v_2653 : reg (bv 128)) => do
      v_5261 <- getRegister v_2653;
      v_5262 <- eval (extract v_5261 0 32);
      v_5263 <- getRegister v_2652;
      v_5264 <- eval (extract v_5263 0 32);
      v_5267 <- eval (extract v_5261 32 64);
      v_5268 <- eval (extract v_5263 32 64);
      v_5271 <- eval (extract v_5261 64 96);
      v_5272 <- eval (extract v_5263 64 96);
      v_5275 <- eval (extract v_5261 96 128);
      v_5276 <- eval (extract v_5263 96 128);
      setRegister (lhs.of_reg v_2653) (concat (mux (ult v_5262 v_5264) v_5262 v_5264) (concat (mux (ult v_5267 v_5268) v_5267 v_5268) (concat (mux (ult v_5271 v_5272) v_5271 v_5272) (mux (ult v_5275 v_5276) v_5275 v_5276))));
      pure ()
    pat_end;
    pattern fun (v_2648 : Mem) (v_2649 : reg (bv 128)) => do
      v_12308 <- getRegister v_2649;
      v_12309 <- eval (extract v_12308 0 32);
      v_12310 <- evaluateAddress v_2648;
      v_12311 <- load v_12310 16;
      v_12312 <- eval (extract v_12311 0 32);
      v_12315 <- eval (extract v_12308 32 64);
      v_12316 <- eval (extract v_12311 32 64);
      v_12319 <- eval (extract v_12308 64 96);
      v_12320 <- eval (extract v_12311 64 96);
      v_12323 <- eval (extract v_12308 96 128);
      v_12324 <- eval (extract v_12311 96 128);
      setRegister (lhs.of_reg v_2649) (concat (mux (ult v_12309 v_12312) v_12309 v_12312) (concat (mux (ult v_12315 v_12316) v_12315 v_12316) (concat (mux (ult v_12319 v_12320) v_12319 v_12320) (mux (ult v_12323 v_12324) v_12323 v_12324))));
      pure ()
    pat_end
