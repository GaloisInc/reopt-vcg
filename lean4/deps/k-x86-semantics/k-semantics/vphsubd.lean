def vphsubd1 : instruction :=
  definst "vphsubd" $ do
    pattern fun (v_3235 : reg (bv 128)) (v_3236 : reg (bv 128)) (v_3237 : reg (bv 128)) => do
      v_9294 <- getRegister v_3235;
      v_9302 <- getRegister v_3236;
      setRegister (lhs.of_reg v_3237) (concat (concat (concat (sub (extract v_9294 32 64) (extract v_9294 0 32)) (sub (extract v_9294 96 128) (extract v_9294 64 96))) (sub (extract v_9302 32 64) (extract v_9302 0 32))) (sub (extract v_9302 96 128) (extract v_9302 64 96)));
      pure ()
    pat_end;
    pattern fun (v_3249 : reg (bv 256)) (v_3250 : reg (bv 256)) (v_3251 : reg (bv 256)) => do
      v_9317 <- getRegister v_3249;
      v_9325 <- getRegister v_3250;
      setRegister (lhs.of_reg v_3251) (concat (concat (concat (concat (sub (extract v_9317 32 64) (extract v_9317 0 32)) (sub (extract v_9317 96 128) (extract v_9317 64 96))) (sub (extract v_9325 32 64) (extract v_9325 0 32))) (sub (extract v_9325 96 128) (extract v_9325 64 96))) (concat (concat (concat (sub (extract v_9317 160 192) (extract v_9317 128 160)) (sub (extract v_9317 224 256) (extract v_9317 192 224))) (sub (extract v_9325 160 192) (extract v_9325 128 160))) (sub (extract v_9325 224 256) (extract v_9325 192 224))));
      pure ()
    pat_end;
    pattern fun (v_3234 : Mem) (v_3230 : reg (bv 128)) (v_3231 : reg (bv 128)) => do
      v_17929 <- evaluateAddress v_3234;
      v_17930 <- load v_17929 16;
      v_17938 <- getRegister v_3230;
      setRegister (lhs.of_reg v_3231) (concat (concat (concat (sub (extract v_17930 32 64) (extract v_17930 0 32)) (sub (extract v_17930 96 128) (extract v_17930 64 96))) (sub (extract v_17938 32 64) (extract v_17938 0 32))) (sub (extract v_17938 96 128) (extract v_17938 64 96)));
      pure ()
    pat_end;
    pattern fun (v_3243 : Mem) (v_3244 : reg (bv 256)) (v_3245 : reg (bv 256)) => do
      v_17948 <- evaluateAddress v_3243;
      v_17949 <- load v_17948 32;
      v_17957 <- getRegister v_3244;
      setRegister (lhs.of_reg v_3245) (concat (concat (concat (concat (sub (extract v_17949 32 64) (extract v_17949 0 32)) (sub (extract v_17949 96 128) (extract v_17949 64 96))) (sub (extract v_17957 32 64) (extract v_17957 0 32))) (sub (extract v_17957 96 128) (extract v_17957 64 96))) (concat (concat (concat (sub (extract v_17949 160 192) (extract v_17949 128 160)) (sub (extract v_17949 224 256) (extract v_17949 192 224))) (sub (extract v_17957 160 192) (extract v_17957 128 160))) (sub (extract v_17957 224 256) (extract v_17957 192 224))));
      pure ()
    pat_end
