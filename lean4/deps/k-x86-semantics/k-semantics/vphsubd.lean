def vphsubd1 : instruction :=
  definst "vphsubd" $ do
    pattern fun (v_3289 : reg (bv 128)) (v_3290 : reg (bv 128)) (v_3291 : reg (bv 128)) => do
      v_9149 <- getRegister v_3289;
      v_9157 <- getRegister v_3290;
      setRegister (lhs.of_reg v_3291) (concat (concat (concat (sub (extract v_9149 32 64) (extract v_9149 0 32)) (sub (extract v_9149 96 128) (extract v_9149 64 96))) (sub (extract v_9157 32 64) (extract v_9157 0 32))) (sub (extract v_9157 96 128) (extract v_9157 64 96)));
      pure ()
    pat_end;
    pattern fun (v_3299 : reg (bv 256)) (v_3300 : reg (bv 256)) (v_3301 : reg (bv 256)) => do
      v_9172 <- getRegister v_3299;
      v_9180 <- getRegister v_3300;
      setRegister (lhs.of_reg v_3301) (concat (concat (concat (concat (sub (extract v_9172 32 64) (extract v_9172 0 32)) (sub (extract v_9172 96 128) (extract v_9172 64 96))) (sub (extract v_9180 32 64) (extract v_9180 0 32))) (sub (extract v_9180 96 128) (extract v_9180 64 96))) (concat (concat (concat (sub (extract v_9172 160 192) (extract v_9172 128 160)) (sub (extract v_9172 224 256) (extract v_9172 192 224))) (sub (extract v_9180 160 192) (extract v_9180 128 160))) (sub (extract v_9180 224 256) (extract v_9180 192 224))));
      pure ()
    pat_end;
    pattern fun (v_3283 : Mem) (v_3284 : reg (bv 128)) (v_3285 : reg (bv 128)) => do
      v_17542 <- evaluateAddress v_3283;
      v_17543 <- load v_17542 16;
      v_17551 <- getRegister v_3284;
      setRegister (lhs.of_reg v_3285) (concat (concat (concat (sub (extract v_17543 32 64) (extract v_17543 0 32)) (sub (extract v_17543 96 128) (extract v_17543 64 96))) (sub (extract v_17551 32 64) (extract v_17551 0 32))) (sub (extract v_17551 96 128) (extract v_17551 64 96)));
      pure ()
    pat_end;
    pattern fun (v_3294 : Mem) (v_3295 : reg (bv 256)) (v_3296 : reg (bv 256)) => do
      v_17561 <- evaluateAddress v_3294;
      v_17562 <- load v_17561 32;
      v_17570 <- getRegister v_3295;
      setRegister (lhs.of_reg v_3296) (concat (concat (concat (concat (sub (extract v_17562 32 64) (extract v_17562 0 32)) (sub (extract v_17562 96 128) (extract v_17562 64 96))) (sub (extract v_17570 32 64) (extract v_17570 0 32))) (sub (extract v_17570 96 128) (extract v_17570 64 96))) (concat (concat (concat (sub (extract v_17562 160 192) (extract v_17562 128 160)) (sub (extract v_17562 224 256) (extract v_17562 192 224))) (sub (extract v_17570 160 192) (extract v_17570 128 160))) (sub (extract v_17570 224 256) (extract v_17570 192 224))));
      pure ()
    pat_end
