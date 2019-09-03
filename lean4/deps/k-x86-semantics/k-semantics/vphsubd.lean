def vphsubd1 : instruction :=
  definst "vphsubd" $ do
    pattern fun (v_3225 : reg (bv 128)) (v_3226 : reg (bv 128)) (v_3227 : reg (bv 128)) => do
      v_9493 <- getRegister v_3225;
      v_9501 <- getRegister v_3226;
      setRegister (lhs.of_reg v_3227) (concat (concat (concat (sub (extract v_9493 32 64) (extract v_9493 0 32)) (sub (extract v_9493 96 128) (extract v_9493 64 96))) (sub (extract v_9501 32 64) (extract v_9501 0 32))) (sub (extract v_9501 96 128) (extract v_9501 64 96)));
      pure ()
    pat_end;
    pattern fun (v_3236 : reg (bv 256)) (v_3237 : reg (bv 256)) (v_3238 : reg (bv 256)) => do
      v_9516 <- getRegister v_3236;
      v_9524 <- getRegister v_3237;
      setRegister (lhs.of_reg v_3238) (concat (concat (concat (concat (sub (extract v_9516 32 64) (extract v_9516 0 32)) (sub (extract v_9516 96 128) (extract v_9516 64 96))) (sub (extract v_9524 32 64) (extract v_9524 0 32))) (sub (extract v_9524 96 128) (extract v_9524 64 96))) (concat (concat (concat (sub (extract v_9516 160 192) (extract v_9516 128 160)) (sub (extract v_9516 224 256) (extract v_9516 192 224))) (sub (extract v_9524 160 192) (extract v_9524 128 160))) (sub (extract v_9524 224 256) (extract v_9524 192 224))));
      pure ()
    pat_end;
    pattern fun (v_3219 : Mem) (v_3220 : reg (bv 128)) (v_3221 : reg (bv 128)) => do
      v_18494 <- evaluateAddress v_3219;
      v_18495 <- load v_18494 16;
      v_18503 <- getRegister v_3220;
      setRegister (lhs.of_reg v_3221) (concat (concat (concat (sub (extract v_18495 32 64) (extract v_18495 0 32)) (sub (extract v_18495 96 128) (extract v_18495 64 96))) (sub (extract v_18503 32 64) (extract v_18503 0 32))) (sub (extract v_18503 96 128) (extract v_18503 64 96)));
      pure ()
    pat_end;
    pattern fun (v_3230 : Mem) (v_3231 : reg (bv 256)) (v_3232 : reg (bv 256)) => do
      v_18513 <- evaluateAddress v_3230;
      v_18514 <- load v_18513 32;
      v_18522 <- getRegister v_3231;
      setRegister (lhs.of_reg v_3232) (concat (concat (concat (concat (sub (extract v_18514 32 64) (extract v_18514 0 32)) (sub (extract v_18514 96 128) (extract v_18514 64 96))) (sub (extract v_18522 32 64) (extract v_18522 0 32))) (sub (extract v_18522 96 128) (extract v_18522 64 96))) (concat (concat (concat (sub (extract v_18514 160 192) (extract v_18514 128 160)) (sub (extract v_18514 224 256) (extract v_18514 192 224))) (sub (extract v_18522 160 192) (extract v_18522 128 160))) (sub (extract v_18522 224 256) (extract v_18522 192 224))));
      pure ()
    pat_end
