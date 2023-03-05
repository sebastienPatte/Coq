BoolHelp.vo BoolHelp.glob BoolHelp.v.beautified BoolHelp.required_vo: BoolHelp.v 
BoolHelp.vio: BoolHelp.v 
BoolHelp.vos BoolHelp.vok BoolHelp.required_vos: BoolHelp.v 
Maps.vo Maps.glob Maps.v.beautified Maps.required_vo: Maps.v PolyDefs.vo BoolHelp.vo Valid.vo
Maps.vio: Maps.v PolyDefs.vio BoolHelp.vio Valid.vio
Maps.vos Maps.vok Maps.required_vos: Maps.v PolyDefs.vos BoolHelp.vos Valid.vos
Valid.vo Valid.glob Valid.v.beautified Valid.required_vo: Valid.v PolyDefs.vo BoolHelp.vo
Valid.vio: Valid.v PolyDefs.vio BoolHelp.vio
Valid.vos Valid.vok Valid.required_vos: Valid.v PolyDefs.vos BoolHelp.vos
PolyDefs.vo PolyDefs.glob PolyDefs.v.beautified PolyDefs.required_vo: PolyDefs.v 
PolyDefs.vio: PolyDefs.v 
PolyDefs.vos PolyDefs.vok PolyDefs.required_vos: PolyDefs.v 
PolyArith.vo PolyArith.glob PolyArith.v.beautified PolyArith.required_vo: PolyArith.v Valid.vo PolyDefs.vo BoolHelp.vo
PolyArith.vio: PolyArith.v Valid.vio PolyDefs.vio BoolHelp.vio
PolyArith.vos PolyArith.vok PolyArith.required_vos: PolyArith.v Valid.vos PolyDefs.vos BoolHelp.vos
PolyVal.vo PolyVal.glob PolyVal.v.beautified PolyVal.required_vo: PolyVal.v PolyDefs.vo Coeff.vo BoolHelp.vo PolyArith.vo Valid.vo
PolyVal.vio: PolyVal.v PolyDefs.vio Coeff.vio BoolHelp.vio PolyArith.vio Valid.vio
PolyVal.vos PolyVal.vok PolyVal.required_vos: PolyVal.v PolyDefs.vos Coeff.vos BoolHelp.vos PolyArith.vos Valid.vos
Coeff.vo Coeff.glob Coeff.v.beautified Coeff.required_vo: Coeff.v Maps.vo BoolHelp.vo PolyArith.vo Valid.vo PolyDefs.vo
Coeff.vio: Coeff.v Maps.vio BoolHelp.vio PolyArith.vio Valid.vio PolyDefs.vio
Coeff.vos Coeff.vok Coeff.required_vos: Coeff.v Maps.vos BoolHelp.vos PolyArith.vos Valid.vos PolyDefs.vos
BTauto.vo BTauto.glob BTauto.v.beautified BTauto.required_vo: BTauto.v PolyDefs.vo PolyVal.vo PolyArith.vo Valid.vo
BTauto.vio: BTauto.v PolyDefs.vio PolyVal.vio PolyArith.vio Valid.vio
BTauto.vos BTauto.vok BTauto.required_vos: BTauto.v PolyDefs.vos PolyVal.vos PolyArith.vos Valid.vos
